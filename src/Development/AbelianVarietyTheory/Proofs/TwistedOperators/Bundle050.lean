module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle041
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle044
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.Analysis.Fourier.FourierTransform
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle001

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}

theorem isSelfDual_iff_vol (h : HasConductor ψ c) (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1 := by
  have := t2Space k
  have hcl : IsClosed (𝒪[k] : Set k) := (isCompact_int k).isClosed
  have hclo : IsClopen (𝒪[k] : Set k) := ⟨hcl, isOpen_int k⟩
  set f : k → ℂ := (𝒪[k] : Set k).indicator 1 with hf
  have hfSB : f ∈ SB k := by
    refine ⟨?_, ?_⟩
    · have hlc := (LocallyConstant.charFn ℂ hclo).isLocallyConstant
      exact hlc
    · exact HasCompactSupport.intro' (isCompact_int k) hcl fun x hx => by simp [f, hx]
  have hf0 : f 0 = 1 := by simp [f]
  have hvol : ν.real (𝒪[k] : Set k) = (ν (𝒪[k] : Set k)).toReal := measureReal_def ν _
  constructor
  · rintro ⟨-, hsd⟩
    have e := (fourier_inversion ν h hfSB).symm.trans (hsd f hfSB)
    rw [hf0, mul_one] at e
    rw [← hvol]
    exact_mod_cast e
  · intro hC
    refine ⟨inferInstance, fun g hg => ?_⟩
    rw [fourier_inversion ν h hg, hvol, hC]
    simp

theorem exists_isSelfDual_of_hasConductor (h : HasConductor ψ c) : ∃ ν : Measure k, IsSelfDual ψ ν := by
  obtain ⟨ν₀, hH, h1⟩ := exists_isUnitVol k
  have hn : 0 < nabs k c := nabs_pos k c
  set a : ℝ≥0 := ⟨(Real.sqrt (nabs k c))⁻¹, by positivity⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have : (Real.sqrt (nabs k c))⁻¹ = 0 := congrArg Subtype.val h0
    have hs : 0 < Real.sqrt (nabs k c) := Real.sqrt_pos.2 hn
    exact (inv_pos.2 hs).ne' this
  have : (a • ν₀).IsAddHaarMeasure := .nnreal_smul ν₀ ha0
  refine ⟨a • ν₀, (isSelfDual_iff_vol h _).2 ?_⟩
  have hval : ((a • ν₀) (𝒪[k] : Set k)).toReal = (Real.sqrt (nabs k c))⁻¹ := by
    rw [smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]
    rfl
  rw [hval, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']

theorem isUnitVol_iff_isSelfDual (h : HasConductor ψ 1) (ν : Measure k) : IsUnitVol ν ↔ IsSelfDual ψ ν := by
  constructor
  · intro hν
    haveI := hν.1
    exact isSelfDual_of_isUnitVol ν h hν
  · intro hsd
    haveI : ν.IsAddHaarMeasure := hsd.1
    have e := (isSelfDual_iff_vol h ν).1 hsd
    rw [nabs_one, mul_one] at e
    have hnn : 0 ≤ (ν (𝒪[k] : Set k)).toReal := ENNReal.toReal_nonneg
    have e1 : (ν (𝒪[k] : Set k)).toReal = 1 := by nlinarith
    exact ⟨hsd.1, (ENNReal.toReal_eq_one_iff _).1 e1⟩

theorem selfDual_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1), (∃ ν : Measure k, IsSelfDual ψ ν) ∧ (HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν ↔ IsSelfDual ψ ν) ∧ ∀ (c : kˣ) (ν : Measure k), HasConductor ψ c → ν.IsAddHaarMeasure → (IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1) := by
  intro k _ _ _ _ _ _ ψ hψ h1
  refine ⟨?_, fun h ν => isUnitVol_iff_isSelfDual h ν, fun c ν hc hν => ?_⟩
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    exact exists_isSelfDual_of_hasConductor hc
  · exact isSelfDual_iff_vol hc ν

end GlobalTheory.SplitWeil
end
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.Mem.Lift.VacAnn

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
private theorem hasFDerivAt_gau {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w : V) :
    HasFDerivAt (_root_.GlobalTheory.RealWeil.gau : V → ℂ)
      ((-(Real.pi : ℂ) * _root_.GlobalTheory.RealWeil.gau w) • ((Complex.ofRealCLM).comp (innerSL ℝ w))) w := by
  have h1 : HasFDerivAt (fun u : V => ‖u‖ ^ 2) (2 • innerSL ℝ w) w := by
    simpa using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt).comp w h1
  have h3 := (h2.const_mul (-(Real.pi : ℂ) / 2)).cexp
  have hf : (_root_.GlobalTheory.RealWeil.gau : V → ℂ) =
      fun u => Complex.exp (-(Real.pi : ℂ) / 2 * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u; unfold _root_.GlobalTheory.RealWeil.gau; push_cast; ring_nf
  rw [hf]
  refine h3.congr_fderiv ?_
  ext y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  push_cast
  ring


open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
theorem _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w v : V) :
    fderiv ℝ (_root_.GlobalTheory.RealWeil.gau : V → ℂ) w v =
      -(Real.pi : ℂ) * ⟪w, v⟫ * _root_.GlobalTheory.RealWeil.gau w := by
  rw [(hasFDerivAt_gau w).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul]
  ring


open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
theorem _root_.GlobalTheory.Mem.Lift.VacAnn.proj_annihilated : ∀ (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V)
    (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) →
    ∀ (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (x : B) (z : V),
      _root_.GlobalTheory.Mem.Lift.dH ρ z (_root_.GlobalTheory.RealWeil.proj h x) +
        I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) (_root_.GlobalTheory.RealWeil.proj h x) = 0 := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h x z
  set P := _root_.GlobalTheory.RealWeil.proj h
  set f := P x with hf_def
  have hf : _root_.GlobalTheory.RealWeil.Sm ρ f :=
    _root_.GlobalTheory.RealWeil.Good.sm hJ
      (_root_.GlobalTheory.RealWeil.Osc.good_proj hJ h x)
  have hsand : ∀ w : V, P (ρ w f) = _root_.GlobalTheory.RealWeil.gau w • f := fun w =>
    _root_.GlobalTheory.RealWeil.proj_heis_proj hJ h w x
  have hcomp : ∀ w v : V, P (ρ w (_root_.GlobalTheory.Mem.Lift.dH ρ v f)) =
      ((Real.pi : ℂ) * I * (⟪w, J v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w
        - (Real.pi : ℂ) * (⟪w, v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w) • f := by
    intro w v
    rw [_root_.GlobalTheory.Mem.Lift.VacBd.heis_dH h hf v w, map_add (f := _), map_smul, hsand w,
      _root_.GlobalTheory.Mem.Lift.VacBd.fderiv_compress P hf _root_.GlobalTheory.RealWeil.contDiff_gau hsand w v,
      _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply, smul_smul, ← add_smul]
    congr 1
    show (Real.pi : ℂ) * I * ((⟪w, J v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w
        + -(Real.pi : ℂ) * ((⟪w, v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w = _
    ring
  set G := _root_.GlobalTheory.Mem.Lift.dH ρ z f + I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) f
  have hG : _root_.GlobalTheory.RealWeil.Sm ρ G :=
    _root_.GlobalTheory.RealWeil.Osc.sm_add (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf z)
      (_root_.GlobalTheory.RealWeil.Osc.sm_smul I (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf (J z)))
  have hzero : ∀ w : V, P (ρ w G) = 0 := by
    intro w
    simp only [G, map_add (f := _), map_smul, hcomp, smul_smul, ← add_smul, hJ z, inner_neg_right]
    apply smul_eq_zero_of_left
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [← (_root_.GlobalTheory.RealWeil.Osc.good_of_sm hJ h hG).inversion hJ]
  have hzero' : ∀ w : V, _root_.GlobalTheory.RealWeil.proj h (ρ (-w) G) = 0 := fun w => hzero (-w)
  simp only [hzero', map_zero, integral_zero]

end GlobalTheory.Mem.Lift.VacAnn
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix

namespace GlobalTheory.SatakeFlip

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem revT_mul (A B : Matrix (Fin n) (Fin n) R) :
    Aᵀ.submatrix Fin.rev Fin.rev * Bᵀ.submatrix Fin.rev Fin.rev = (B * A)ᵀ.submatrix Fin.rev Fin.rev := by
  rw [transpose_mul]
  exact submatrix_mul_equiv Aᵀ Bᵀ Fin.rev Fin.revPerm Fin.rev

theorem revT_one : (1 : Matrix (Fin n) (Fin n) R)ᵀ.submatrix Fin.rev Fin.rev = 1 := by
  rw [transpose_one]
  exact submatrix_one_equiv Fin.revPerm

def invRevT : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).valᵀ.submatrix Fin.rev Fin.rev, g.valᵀ.submatrix Fin.rev Fin.rev,
    by rw [revT_mul, Units.mul_inv, revT_one], by rw [revT_mul, Units.inv_mul, revT_one]⟩
  map_one' := Units.ext (by simp only [inv_one, Units.val_one]; exact revT_one)
  map_mul' g h := Units.ext (by simp only [_root_.mul_inv_rev, Units.val_mul]; rw [revT_mul])

theorem invRevT_apply (g : GL (Fin n) R) (i j : Fin n) :
    (invRevT g).val i j = (g⁻¹).val j.rev i.rev := rfl

theorem invRevT_invRevT (g : GL (Fin n) R) : invRevT (invRevT g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invRevT_apply, ← map_inv, invRevT_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem invRevT_mem_borel {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) :
    invRevT b ∈ GlobalTheory.SmGL.borel R (Fin n) :=
  (mem_borel R).2 fun _ _ h => (mem_borel R).1 (inv_mem hb) _ _ (Fin.rev_lt_rev.2 h)

theorem inv_diag_mul {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) (i : Fin n) :
    (b⁻¹).val i i * b.val i i = 1 := by
  have h := congrFun (congrFun (Units.inv_mul b) i) i
  change ((b⁻¹).val * b.val) i i = (1 : Matrix (Fin n) (Fin n) R) i i at h
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_single i] at h
  · exact h
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h' | h'
    · rw [(mem_borel R).1 (inv_mem hb) _ _ h', zero_mul]
    · rw [(mem_borel R).1 hb _ _ h', mul_zero]
  · simp

end Ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem invRevT_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : invRevT g ∈ KO k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => h2 _ _, fun i j => ?_⟩
  rw [← map_inv, invRevT_apply, inv_inv]
  exact h1 _ _

theorem ord_inv_eq_neg (x : kˣ) : ord k x⁻¹ = -ord k x := by
  have h := ord_mul k x⁻¹ x
  rw [inv_mul_cancel, ord_eq_zero (k := k) (x := 1) (by simp)] at h
  omega

def cosetMap : GL (Fin n) k ⧸ KO k (Fin n) → GL (Fin n) k ⧸ KO k (Fin n) :=
  Quotient.map' invRevT fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact invRevT_mem_KO h

theorem cosetMap_mk (g : GL (Fin n) k) :
    cosetMap (g : GL (Fin n) k ⧸ KO k (Fin n)) = (invRevT g : GL (Fin n) k) := rfl

theorem cosetMap_cosetMap (c : GL (Fin n) k ⧸ KO k (Fin n)) : cosetMap (cosetMap c) = c := by
  induction c using QuotientGroup.induction_on with
  | H g => rw [cosetMap_mk, cosetMap_mk, invRevT_invRevT]

theorem cosetMap_smul (x : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    cosetMap (x • c) = invRevT x • cosetMap c := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, cosetMap_mk, cosetMap_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      smul_eq_mul, map_mul]

theorem exists_isBorelSph_rev_inv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ)
    (h : IsBorelSph k γ φ) (hS : HasBoundedSums k φ) :
    ∃ ψ : GL (Fin n) k → ℂ, IsBorelSph k (fun i => (γ (Fin.rev i))⁻¹) ψ ∧ HasBoundedSums k ψ := by
  classical
  refine ⟨fun g => φ (invRevT g), ⟨fun g x hx => ?_, fun b hb t ht => ?_⟩, fun S hK => ?_⟩
  · show φ (invRevT (g * x)) = φ (invRevT g)
    rw [map_mul, h.1 _ _ (invRevT_mem_KO hx)]
  · show φ (invRevT b) = _
    rw [h.2 _ (invRevT_mem_borel hb) (fun i => (t i.rev)⁻¹) fun i => ?_]
    · refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, ord_inv_eq_neg, _root_.zpow_neg, _root_.inv_zpow]
    · rw [invRevT_apply, Units.val_inv_eq_inv_val, ← ht]
      exact eq_inv_of_mul_eq_one_left (inv_diag_mul hb _)
  · have hinj : Function.Injective (cosetMap (k := k) (n := n)) :=
      Function.LeftInverse.injective cosetMap_cosetMap
    have h1 := hS (S.image cosetMap) fun x hx c hc => by
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
      refine Finset.mem_image.2 ⟨invRevT x • d, hK _ (invRevT_mem_KO hx) _ hd, ?_⟩
      rw [cosetMap_smul, invRevT_invRevT]
    rw [Finset.card_image_of_injective _ hinj, Finset.sum_image fun _ _ _ _ e => hinj e] at h1
    refine le_of_eq_of_le (congrArg _ (Finset.sum_congr rfl fun c _ => ?_)) h1
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (invRevT c.out)
    rw [← cosetMap_mk, QuotientGroup.out_eq'] at hx
    show φ (invRevT c.out) = _
    rw [hx, h.1 _ _ x.2]

end GlobalTheory.SatakeFlip
end
end

section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap

open scoped FourierTransform RealInnerProductSpace Real

namespace GlobalTheory.RealWeil

theorem eq_zero_of_inner_rhoSch_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l),
    (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume)
      (k.toLp 2 volume) = 0) → k = 0 := by
  intro l _ k h
  set G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  let m : EuclideanSpace ℝ l → ℂ := fun x => G x * k x
  have hGn : ∀ x, ‖G x‖ ≤ 1 := fun x => by
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := Real.pi_pos
    nlinarith [sq_nonneg ‖x‖]
  have hm_cont : Continuous m := G.continuous.mul k.continuous
  have hm_int : Integrable m := k.integrable.norm.mono' hm_cont.aestronglyMeasurable
    (ae_of_all _ fun x => by
      simp only [m, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hGn x))
  have hF : 𝓕 m = 0 := by
    funext q
    have hq := h (Sum.elim 0 (fun i => q i))
    have hp : pPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = 0 := by
      ext i; simp [pPart]
    have hqq : qPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = q := by
      ext i; simp [qPart]
    rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume] at hq
    rw [Real.fourier_eq', Pi.zero_apply, ← hq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [m, coe_rhoSch, rhoFun, phase, hp, hqq, add_zero, inner_zero_left, mul_zero, RCLike.inner_apply,
      map_mul, smul_eq_mul]
    rw [← Complex.exp_conj]
    have hGc : (starRingEnd ℂ) (G x) = G x := by
      rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [hGc]
    have : (starRingEnd ℂ) (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * Complex.I) =
        ((-2 * π * ⟪x, q⟫ : ℝ) : ℂ) * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I, real_inner_comm]
      push_cast
      ring
    rw [this]
    ring
  have hm0 : m = 0 := by
    have hi : Integrable (𝓕 m) := by rw [hF]; exact integrable_zero _ _ _
    rw [← hm_cont.fourierInv_fourier_eq hm_int hi, hF]
    funext v
    simp [Real.fourierInv_eq]
  ext x
  have hx := congrFun hm0 x
  simp only [m, Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with hx | hx
  · exfalso
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_eq_zero] at hx
    exact (Real.exp_pos _).ne' hx
  · simpa using hx

end GlobalTheory.RealWeil
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.fourier_inversion_zero_compact_quotient : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] [Countable A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) → Φ 0 = ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ := by
  first | exact @GlobalTheory.CompactQuotientFourier.inversion_at_zero | exact GlobalTheory.CompactQuotientFourier.inversion_at_zero | (intros; apply GlobalTheory.CompactQuotientFourier.inversion_at_zero <;> assumption)
end

section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix
open scoped TensorProduct

namespace GlobalTheory.LocalThetaGL

section Abstract

variable {H V W U Y Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Y] [Module ℂ Y] {P : Subgroup H}

end Abstract

section Regular

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] {π : Representation ℂ G V}

end Regular

section Local

open GlobalTheory.IndefiniteRowSideFullHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

theorem compact_open_basis (n : Type) [Fintype n] [DecidableEq n] : ∀ U ∈ nhds (1 : GL n k),
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end Local

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Main

section Final

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end Final

end GlobalTheory.LocalThetaGL
end
end
