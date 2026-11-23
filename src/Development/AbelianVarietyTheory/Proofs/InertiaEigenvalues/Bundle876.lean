module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitEmbeddingValuedEqIntValuationInteger
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem map_infPart_of_nsmul {V W : HSp D} {y : WO V W} {M : ℕ} (hM : M ≠ 0) (h : (M • y).map (infPart D) = 0) :
    y.map (infPart D) = 0 := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul D.host.F] at h1
  exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hM)

theorem map_infPart_of_mem_latO {V W : HSp D} {LV : Set (Fin V.rank → D.host.E)} {LW : Set (Fin W.rank → D.host.E)}
    {u : WO V W} (hu : u ∈ latO V W LV LW fun _ => True) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add (f := _), hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem trSp_theta_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (e : AE D) (M : ℕ) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁,
      IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv e M O₁ hM f hf
  have hvac : IsVacO ψ θ V W (fun _ => 1) sW (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f₀ :=
    hv.2.2.2.2.2.2.2.2
  let Sp : Submodule ℂ (WO V W → ℂ) :=
    Submodule.span ℂ (Set.range fun a : {a : WO V W // a.map (infPart D) = 0} => heisO ψ V W a f₀)
  have hle : trSp ψ V W ΛV ΛW f₀ e M O₁ ≤ Sp.restrictScalars O₁ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, -, hy, rfl⟩
    exact Submodule.subset_span ⟨⟨y, map_infPart_of_nsmul hM (map_infPart_of_mem_latO hy)⟩, rfl⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hle hf)
  rw [← hc]
  exact ⟨GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ V W hvac.1.1 f₀ hvac.2.theta _ c.support (fun a => a.1) c
      fun a _ => a.2,
    fun τ => GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ V W hvac.1.1 hvac.2.inf f₀ hvac.2.theta τ _ (hvac.2.fock τ) _
      c.support (fun a => a.1) c fun a _ => a.2⟩

end GlobalTheory.LevelSeries
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.ThetaPoisson GroundTheory.Global
open scoped ComplexConjugate nonZeroDivisors

namespace GlobalTheory.RSTheta

section Row

variable {R : Type} [CommRing R] {a : ℕ}

def rowMat (ℓ : Fin a) (y : Fin a → R) : Matrix (Fin a) (Fin a) R := (1 : Matrix (Fin a) (Fin a) R).updateRow ℓ y

theorem det_rowMat (ℓ : Fin a) (y : Fin a → R) : (rowMat ℓ y).det = y ℓ := by
  have h := det_updateRow_sum (1 : Matrix (Fin a) (Fin a) R) ℓ y
  have e : ∑ k, y k • (1 : Matrix (Fin a) (Fin a) R) k = y := by
    funext j
    simp [Matrix.one_apply, Finset.sum_apply]
  rw [e] at h
  simpa [rowMat] using h

theorem isUnit_rowMat_iff {ℓ : Fin a} {y : Fin a → R} : IsUnit (rowMat ℓ y) ↔ IsUnit (y ℓ) := by
  rw [isUnit_iff_isUnit_det, det_rowMat]


open Classical in
def rowGL (ℓ : Fin a) (y : Fin a → R) : GL (Fin a) R :=
  if h : IsUnit (y ℓ) then (isUnit_rowMat_iff.2 h).unit else 1

theorem val_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) : (rowGL ℓ y).val = rowMat ℓ y := by
  rw [rowGL, dite_eq_left h, IsUnit.unit_spec]

theorem single_vecMul_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) :
    Pi.single ℓ 1 ᵥ* (rowGL ℓ y).val = y := by
  rw [val_rowGL h, single_one_vecMul]
  exact updateRow_self

theorem rowGL_single (ℓ : Fin a) : rowGL ℓ (Pi.single ℓ (1 : R)) = 1 := by
  refine Units.ext ((val_rowGL (by simp)).trans ?_)
  have : (Pi.single ℓ 1 : Fin a → R) = (1 : Matrix (Fin a) (Fin a) R) ℓ := by
    funext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [rowMat, this]
  exact updateRow_eq_self _ _

end Row

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
variable (E) in
def rowSet (ℓ : Fin a) : Set (Fin a → Cinf E) := {u | ∀ w, u ℓ w ≠ 0}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem isUnit_of_mem_rowSet {ℓ : Fin a} {u : Fin a → Cinf E} (h : u ∈ rowSet E ℓ) : IsUnit (u ℓ) :=
  Pi.isUnit_iff.2 fun w => (h w).isUnit

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpen_rowSet (ℓ : Fin a) : IsOpen (rowSet E ℓ) := by
  rw [rowSet, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuousOn_rowGL (ℓ : Fin a) : ContinuousOn (rowGL ℓ) (rowSet E ℓ) := by
  refine GlobalTheory.CuspQuot.isOpenEmbedding_val.isInducing.continuousOn_iff.2 ?_
  have h : Continuous fun u : Fin a → Cinf E => rowMat ℓ u := continuous_const.matrix_updateRow ℓ continuous_id
  exact h.continuousOn.congr fun u hu => val_rowGL (isUnit_of_mem_rowSet hu)

def rsInf (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (g : GA E a) (u : Fin a → Cinf E) : ℂ :=
  φ (g * (infGL E a (rowGL ℓ u))⁻¹) * conj (φ' (g * (infGL E a (rowGL ℓ u))⁻¹)) * Φ u

def rsPsi (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  thetaFn (rsInf ℓ φ φ' Φ g) J η y

theorem rsPsi_ratGL_mul (ℓ : Fin a) {φ φ' : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h' : ∀ γ g, φ' (ratGL E a γ * g) = φ' g) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (γ : GL (Fin a) E) (g : GA E a) (y : Fin a → Ad E) :
    rsPsi ℓ φ φ' Φ J η (ratGL E a γ * g) y = rsPsi ℓ φ φ' Φ J η g y := by
  simp only [rsPsi, thetaFn, rsInf, mul_assoc, h, h']

theorem continuousOn_inv_rowGL (ℓ : Fin a) :
    ContinuousOn (fun u => (infGL E a (rowGL ℓ u))⁻¹) (rowSet E ℓ) :=
  (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn (continuousOn_rowGL ℓ)).inv

theorem continuous_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hp : p.2 ∈ tsupport Φ
  · have h1 : ContinuousAt (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) p :=
      continuousAt_fst.mul (ContinuousAt.comp (f := Prod.snd)
        ((continuousOn_inv_rowGL ℓ).continuousAt ((isOpen_rowSet ℓ).mem_nhds (hs hp))) continuousAt_snd)
    exact ((h.continuousAt.comp h1).mul ((Complex.continuous_conj.comp h').continuousAt.comp h1)).mul
      (hΦ.comp continuous_snd).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuousAt_snd.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [rsInf, hq]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpen_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsOpen (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => (isOpen_idealFiniteAdeles J).preimage (continuous_apply i)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isCompact_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsCompact (latt a J) :=
  isCompact_pi_infinite fun _ => isCompact_idealFiniteAdeles J

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isClosed_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsClosed (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isClosed_iInter fun i =>
    (AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles J)).preimage (continuous_apply i)

theorem continuous_rsPsi {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) : Continuous fun p : GA E a × (Fin a → Ad E) => rsPsi ℓ φ φ' Φ J η p.1 p.2 := by
  have h1 : Continuous fun p : GA E a × (Fin a → Ad E) => (p.1, fun i => pInf E (p.2 i)) :=
    continuous_fst.prodMk (continuous_pi fun i =>
      GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_snd))
  have h2 : Continuous fun p : GA E a × (Fin a → Ad E) => (fun i => pFin E (p.2 i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp
      ((continuous_apply i).comp continuous_snd)).sub continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    (IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const)
  exact ((continuous_rsInf h h' hΦ hs).comp h1).mul (h3.comp h2)

theorem continuous_of_mem_smoothSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hS := GlobalTheory.ShortVecDecay.smoothSpan_le_Sm π (Submodule.subset_span hF)
    obtain ⟨f, φ, hf, hφ, rfl⟩ := hF
    refine ContAut.continuous_of_isOpen_stab E a ⟨_, hS⟩ (isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      ((π.cusp φ hφ).1.level.mem_nhds (by simp)) fun k hk => Subtype.ext (funext fun g => ?_)))
    have e : (fun x => φ.1 (x * finGL E a k)) = φ.1 := congrArg Subtype.val hk
    exact (GlobalTheory.JSW.smoothInf_rt_fin f φ.1 k g).symm.trans (by rw [e])
  | zero => exact continuous_const
  | add F G _ _ hF hG => exact hF.add hG
  | smul z F _ hF => exact hF.const_smul z

theorem continuous_of_mem_or {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous φ.1 :=
  h.elim (fun h => ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ h).1.level) continuous_of_mem_smoothSpan

end GlobalTheory.RSTheta

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
namespace GlobalTheory.IdemKerDiv

theorem resS_eq_zero_iff_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (PP : Pl E) (x : Formalism.L2.Herm.intAf F E) :
    resS F PP x = 0 ↔ x ∈ idS F PP.asIdeal := by
  simp [resS, Ideal.Quotient.eq_zero_iff_mem]

theorem intAt_inv_mul {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    {ϖ p : 𝓞 E} (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (hp : p ∈ P.asIdeal) :
    Formalism.L2.Col.IntAt P ((ϖ : E)⁻¹ * (p : E)) := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hϖ2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : P.asIdeal ∣ Ideal.span {ϖ} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖ)
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hϖ2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  have hsp : s * p ∈ Ideal.span {ϖ} := by
    rw [hJ, mul_comm s p]; exact Ideal.mul_mem_mul hp hsJ
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hsp
  refine ⟨r, s, hsP, ?_⟩
  have hϖE : (ϖ : E) ≠ 0 := by exact_mod_cast hϖ0
  have h1 : (r : E) * (ϖ : E) = (s : E) * (p : E) := by exact_mod_cast hr
  show (s : E) * ((ϖ : E)⁻¹ * (p : E)) = (r : E)
  field_simp
  linear_combination -h1



theorem integral_div_iff : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → ∀ N : EAf D, ∀ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N → (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = 0) := by
  intro D Q es ϖ hid horth hϖ N hN hfix
  have hE : ∀ P ∈ Q, toEAf D (es P) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun P hP => (GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hid P hP)).1
  have hϖ0 : ∀ P ∈ Q, ((ϖ P : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro P hP h
    have : ϖ P = 0 := by exact_mod_cast h
    exact (hϖ P hP).2 (this ▸ Ideal.zero_mem _)
  have hmul : ∀ P ∈ Q, ∀ P' ∈ Q, es P * es P' = if P = P' then es P else 0 := by
    intro P hP P' hP'
    split_ifs with h
    · subst h; exact (hid P hP).1.1
    · exact GlobalTheory.SplitIdeleModulus.idemAt_mul_eq_zero (hid P hP) (hid P' hP') h
  have hpp : (∑ P ∈ Q, es P * incA D ((ϖ P : D.host.E))) *
      (∑ P ∈ Q, es P * incA D ((ϖ P : D.host.E)⁻¹)) = ∑ P ∈ Q, es P := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    rw [Finset.sum_eq_single P]
    · calc es P * incA D (ϖ P : D.host.E) * (es P * incA D ((ϖ P : D.host.E))⁻¹)
            = (es P * es P) * incA D ((ϖ P : D.host.E) * (ϖ P : D.host.E)⁻¹) := by
              rw [map_mul]; ring
          _ = es P := by rw [(hid P hP).1.1, mul_inv_cancel₀ (hϖ0 P hP), map_one, mul_one]
    · intro P' hP' hne
      calc es P * incA D (ϖ P : D.host.E) * (es P' * incA D ((ϖ P' : D.host.E))⁻¹)
            = (es P * es P') * incA D ((ϖ P : D.host.E) * (ϖ P' : D.host.E)⁻¹) := by
              rw [map_mul]; ring
          _ = 0 := by rw [hmul P hP P' hP', if_neg (Ne.symm hne), zero_mul]
    · intro h; exact absurd hP h
  have hoToS : ∀ x : 𝓞 D.host.E,
      ((oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
        toEAf D (incA D (x : D.host.E)) := by
    intro x; rw [GlobalTheory.IdemIntegral.toEAf_incA]; rfl
  constructor
  · intro hM PP hPP
    refine (resS_eq_zero_iff_mem (F := D.host.F) (E := D.host.E) PP ⟨N, hN⟩).mpr ?_
    obtain ⟨M, hMdef⟩ : ∃ M, M = toEAf D (∑ P ∈ Q, es P * incA D ((ϖ P : D.host.E))⁻¹) * N :=
      ⟨_, rfl⟩
    rw [← hMdef] at hM
    let eI : Pl D.host.E → Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun P => if h : P ∈ Q then ⟨toEAf D (es P), hE P h⟩ else 0
    have hsplit : (⟨N, hN⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        (∑ P ∈ Q, eI P * oToS D.host.F D.host.E (ϖ P)) * ⟨M, hM⟩ := by
      apply Subtype.ext
      have hs : ((∑ P ∈ Q, eI P * oToS D.host.F D.host.E (ϖ P) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
          toEAf D (∑ P ∈ Q, es P * incA D ((ϖ P : D.host.E))) := by

        rw [map_sum]
        push_cast
        apply Finset.sum_congr rfl
        intro P hP
        simp only [eI, dif_pos hP, map_mul, hoToS]
      show N = ((∑ P ∈ Q, eI P * oToS D.host.F D.host.E (ϖ P) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) * M
      rw [hs, hMdef, ← mul_assoc, ← map_mul, hpp, hfix]
    rw [hsplit]
    refine Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun P hP => ?_)
    by_cases hPe : P = PP
    · subst hPe
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hϖ P hP).1)
    · refine Ideal.mul_mem_right _ _ ?_
      refine (resS_eq_zero_iff_mem (F := D.host.F) (E := D.host.E) PP _).mp ?_
      simp only [eI, dif_pos hP]
      exact GlobalTheory.TameProd.resS_idem_eq_zero (hid P hP) hPe _
  · intro hres

    rw [map_sum, Finset.sum_mul]
    refine Subring.sum_mem _ fun P hP => ?_
    have hmem : (⟨N, hN⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈
        Ideal.map (oToS D.host.F D.host.E) P.asIdeal :=
      (resS_eq_zero_iff_mem (F := D.host.F) (E := D.host.E) P ⟨N, hN⟩).mp (hres P hP)
    have key : ∀ x : Formalism.L2.Herm.intAf D.host.F D.host.E,
        x ∈ Ideal.map (oToS D.host.F D.host.E) P.asIdeal →
        toEAf D (es P * incA D ((ϖ P : D.host.E))⁻¹) * (x : EAf D) ∈
          Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro x hx
      change x ∈ Submodule.span _ _ at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, hp, rfl⟩ := hy
        rw [hoToS, ← map_mul, mul_assoc, ← map_mul]
        exact GlobalTheory.IdemIntegral.mem_of_idemAt (hid P hP) (intAt_inv_mul P (hϖ P hP).1 (hϖ P hP).2 hp)
      | zero => simp
      | add a b _ _ ha hb =>
        rw [Subring.coe_add, mul_add]; exact add_mem ha hb
      | smul a b _ hb =>
        rw [smul_eq_mul, Subring.coe_mul, mul_left_comm]; exact mul_mem a.2 hb
    exact key _ hmem

end GlobalTheory.IdemKerDiv
end
