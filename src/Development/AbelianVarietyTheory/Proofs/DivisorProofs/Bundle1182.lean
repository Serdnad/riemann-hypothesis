module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle310
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Mathlib.Topology.Sheaves.Presheaf
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem GlobalTheory.DefPt.det_gramPl_smul_single : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (eqv : ι ≃ Fin n) (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → ∀ (t : K) (v : InfinitePlace K), (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K))).det.re = ‖v.embedding t‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 := by
  intro K _ _ _ ι _ _ n eqv Y hY t v
  have hinv : ((Y v.embedding)⁻¹)⁻¹ = Y v.embedding :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 (hY _))
  have hf : ∀ a : ι, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (t • (Pi.single a 1 : ι → K)) = fun i => v.embedding t * Y v.embedding i a := by
    intro a
    funext i
    simp only [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, hinv, Matrix.mulVec, dotProduct, Pi.basisFun_repr,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have hg : Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K)) =
      ((‖v.embedding t‖ ^ 2 : ℝ) : ℂ) • Matrix.reindex eqv eqv ((Y v.embedding)ᴴ * Y v.embedding) := by
    ext a b
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hf, Matrix.of_apply, Matrix.smul_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply,
      smul_eq_mul, Finset.mul_sum, star_mul']
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.conj_mul' (v.embedding t)
    push_cast
    rw [← this]
    simp only [RCLike.star_def]
    ring
  rw [hg, Matrix.det_smul, Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin,
    RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, ← pow_mul]
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

open scoped WithZero

namespace GlobalTheory.CdvrPlaceVal

theorem mem_range_iff_valV_le_one (T : CDVR) (x : T.Fr) :
    x ∈ Set.range (algebraMap T.V T.Fr) ↔ valV T.V x ≤ 1 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ v
  · intro hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
      (IsDiscreteValuationRing.maximalIdeal T.V) x hx
    have hu : IsUnit (d : T.V) := by
      by_contra hu
      exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 hu)
    obtain ⟨u, hu⟩ := hu
    refine ⟨n * ↑u⁻¹, ?_⟩
    rw [map_mul, ← hnd, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

theorem vV_eq_mul_vAdd (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR)
    (iK : K →+* T.Fr)
    (h : ∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) :
    ∃ e : ℕ, 0 < e ∧ ∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z := by
  let v1 : Valuation K ℤᵐ⁰ := (valV T.V).comap iK
  have hv1 : ∀ z, v1 z = valV T.V (iK z) := fun z => rfl
  have hle : ∀ z : K, v1 z ≤ 1 ↔ 𝔓.valuation K z ≤ 1 := fun z => by
    rw [← h z, mem_range_iff_valV_le_one, hv1]
  have hunit : ∀ w : K, 𝔓.valuation K w = 1 → v1 w = 1 := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have h0 : v1 w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
    have h1 : v1 w ≤ 1 := (hle w).2 hw.le
    have h2 : v1 w⁻¹ ≤ 1 := (hle w⁻¹).2 (by rw [map_inv₀, hw, inv_one])
    rw [map_inv₀] at h2
    have h1' := (WithZero.log_le_log h0 one_ne_zero).2 h1
    have h2' := (WithZero.log_le_log (inv_ne_zero h0) one_ne_zero).2 h2
    rw [WithZero.log_inv, WithZero.log_one] at h2'
    rw [WithZero.log_one] at h1'
    rw [← WithZero.exp_log h0, show WithZero.log (v1 w) = 0 by omega]
    rfl
  obtain ⟨ϖ, hϖ⟩ := 𝔓.valuation_exists_uniformizer K
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hv1ϖ0 : v1 ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  have hlt : v1 ϖ < 1 := by
    have hle1 : v1 ϖ ≤ 1 := (hle ϖ).2 (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    refine lt_of_le_of_ne hle1 fun heq => ?_
    have h3 : v1 ϖ⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have h4 := (hle ϖ⁻¹).1 h3
    rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg] at h4
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h4
    norm_num at h4
  have ha : 0 < vV T.V (iK ϖ) := by
    have h5 : WithZero.log (v1 ϖ) < WithZero.log 1 := (WithZero.log_lt_log hv1ϖ0 one_ne_zero).2 hlt
    rw [WithZero.log_one, hv1] at h5
    simp only [vV]
    omega
  refine ⟨(vV T.V (iK ϖ)).toNat, by omega, fun z => ?_⟩
  rw [Int.toNat_of_nonneg ha.le]
  by_cases hz : z = 0
  · subst hz; simp [vV, vAdd]
  have hz2 : 𝔓.valuation K z = WithZero.exp (-vAdd 𝔓 z) := by
    simp only [vAdd, neg_neg]; exact (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hz)).symm
  have hw : 𝔓.valuation K (z * ϖ ^ (-vAdd 𝔓 z)) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, hz2, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu := hunit _ hw
  have hz' : z = (z * ϖ ^ (-vAdd 𝔓 z)) * ϖ ^ (vAdd 𝔓 z) := by
    rw [mul_assoc, ← zpow_add₀ hϖ0]; simp
  have hv : v1 z = v1 ϖ ^ (vAdd 𝔓 z) := by
    conv_lhs => rw [hz']
    rw [map_mul, hu, one_mul, map_zpow₀]
  have e1 : vV T.V (iK z) = -WithZero.log (v1 z) := rfl
  have e2 : vV T.V (iK ϖ) = -WithZero.log (v1 ϖ) := rfl
  rw [e1, e2, hv, WithZero.log_zpow, smul_eq_mul]
  ring

end GlobalTheory.CdvrPlaceVal
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorProof

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct

def WeilUnique (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f

def WeilChange (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT νS νT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 →
    ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h)

variable {D : D7}

theorem isHeckeChar_mul_inv {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2, inv_one, mul_one]⟩

theorem isDetRoot_one (V : HSp D) : IsDetRoot V 1 1 := by
  unfold IsDetRoot
  rw [map_one, Units.val_one, Units.val_one, Matrix.det_one, map_one, one_mul]

theorem weil_ratio (hU : WeilUnique D) (hC : WeilChange D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT χS' χT' : (AE D)ˣ →* Circle} {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (ho : IsWeilDatumO ψ S T χS χT om) (ho' : IsWeilDatumO ψ S T χS' χT' om') {g : GA D S} {h : GA D T}
    {x y : (AE D)ˣ} (hx : IsDetRoot S g x) (hy : IsDetRoot T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om' (g, h) f = ((((χT' x * (χT x)⁻¹)⁻¹ * (χS' y * (χS y)⁻¹) : Circle) : ℂ)) • om (g, h) f := by
  obtain ⟨o, h1, h2⟩ := hC ψ ho.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om ho
    (isHeckeChar_mul_inv ho'.hecS ho.hecS) (isHeckeChar_mul_inv ho'.hecT ho.hecT)
    (resEta_parity (resEta_mul ho'.resS (resEta_inv ho.resS)) (by omega))
    (resEta_parity (resEta_mul ho'.resT (resEta_inv ho.resT)) (by omega))
  have e : ∀ a b : (AE D)ˣ →* Circle, a * (b * a⁻¹) = b := fun a b => by
    ext1 z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (b z), mul_inv_cancel_left]
  rw [e, e] at h1
  rw [hU ψ ho.std S T χS' χT' om' o ho' h1 _ f hf, h2 g h x y hx hy]
  rfl

theorem vac_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := h.2.norm
  have := hn p hp
  simp [nrm2] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem frame_ratio (hU : WeilUnique D) (hC : WeilChange D) (hω : R.thP_ωP) (i : Fin D.R.m) (t t' : T0)
    {h : GA D (Wc D i)} {x : (AE D)ˣ} (hx : IsDetRoot (Wc D i) h x) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) :
    ((R.xi t x : Circle) : ℂ) • R.ωP i t' (1, h) f = ((R.xi t' x : Circle) : ℂ) • R.ωP i t (1, h) f := by
  rw [weil_ratio hU hC (hω i t) (hω i t') (isDetRoot_one _) hx hf, smul_smul, ← Circle.coe_mul]
  congr 2
  show R.xi t x * (_ * (R.mu0 _ x * R.xi t' x * (R.mu0 _ x * R.xi t x)⁻¹)) = _
  rw [map_one, map_one, mul_inv_cancel, inv_one, one_mul, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul,
    mul_comm (R.xi t' x), mul_inv_cancel_left]

end GlobalTheory.TwistFactorProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.StandardLattice (stdForm stdLat)
open Formalism.HermitianLatticesTheory (gmap isom genus)

namespace GlobalTheory

namespace StdMassBound

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def matEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin γ) (Matrix.mulVecLin γ.conjTranspose)
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])

theorem matEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    matEquiv γ h ∈ isom (stdForm E n) := by
  intro x y
  change star (γ.mulVec x) ⬝ᵥ (γ.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, mul_eq_one_comm.1 h, Matrix.one_mulVec]

theorem diagForm_eq : Examples₂.diagForm (E := E) n (fun _ => false) = stdForm E n := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  change ∑ i, star (x i) * Examples₂.sgn false * y i = ∑ i, star (x i) * y i
  simp [Examples₂.sgn]

variable [NumberField E]

omit [StarRing E] in
theorem stdLat_eq : Examples₂.stdLat (E := E) n = stdLat E n := by
  unfold Examples₂.stdLat stdLat
  congr 2
  funext i
  exact Pi.basisFun_apply E (Fin n) i

omit [StarRing E] in
theorem mem_one_iff (a : E) : a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

theorem selfDual_of_mem_genus {M : Submodule (𝓞 E) (Fin n → E)} (hM : M ∈ genus (stdForm E n) (stdLat E n))
    (y : Fin n → E) : y ∈ M ↔ ∀ x ∈ M, IsIntegral ℤ (∑ i, star (x i) * y i) := by
  have hsym : (stdForm E n).IsSymm := diagForm_eq (E := E) (n := n) ▸ Examples₂.diagForm_isSymm n _
  obtain ⟨-, -, hinv⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 E) E (Fin n → E) (stdForm E n) hsym
    (Examples₂.star_integral Examples₂.star_isIntegral)
  have h0 : Formalism.HermitianLatticesTheory.IsUnimodular (stdForm E n) (stdLat E n) := by
    rw [← diagForm_eq, ← stdLat_eq]
    exact Examples₂.stdLat_unimod Examples₂.star_isIntegral n _
  have hfg : (stdLat E n).FG := Submodule.fg_span (Set.finite_range _)
  have hu : Formalism.HermitianLatticesTheory.dual (stdForm E n) M = M := ((hinv _ _ hfg hM.1.fg hM.2).1).1 h0
  conv_lhs => rw [← hu]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, mem_one_iff]
  rfl

end StdMassBound


open StdMassBound in
theorem mass_stdLat_le :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) ≤
      (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * n ^ 2) := by
  intro E _ _ _ _ hs n
  have hexists : ∃ R : Finset (Submodule (𝓞 E) (Fin n → E)),
      (R.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG →
        (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i)) →
        ∃ L₀ ∈ R, ∃ γ : Matrix (Fin n) (Fin n) E,
          γ * (γ.map (IsCMField.complexConj E)).transpose = 1 ∧
          ∀ x, x ∈ L₀ ↔ γ.mulVec x ∈ L := by
    open RootClassCount ReciprocityTheory.ChartRestriction.G.FD in
    obtain ⟨R, -, h2, h3⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
      {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)}
      (B := 4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2) (by positivity) fun L hL =>
        ⟨by simp, fun x hx => (hL.2 x).1 hx,
          exists_bounded_basis L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
    refine ⟨R, h3.trans ?_, fun L hfg hsd => ?_⟩
    · have h := bound_le (fdeg E) n ClassCount.fdeg_pos (one_le_rootDiscr (E := E))
      rw [← ShortVectors.finrank_eq] at h
      rw [rdE_eq, ← ShortVectors.finrank_eq]
      exact h
    · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hfg, fun y => by
        simp only [isIntegral_herm_iff]; exact hsd y⟩
      exact ⟨L₀, hL₀, γ, mul_conjTranspose_eq_one _ hγ, hm⟩
  obtain ⟨R, hR, H⟩ := hexists
  refine le_trans ?_ hR
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs with hex
  swap
  · positivity
  obtain ⟨h1, h2⟩ := hex.choose_spec
  generalize hex.choose = s at h1 h2
  have key : ∀ M ∈ s, ∃ L₀ ∈ R, ∃ g ∈ isom (stdForm E n), gmap g L₀ = M := by
    intro M hM
    obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H M (h1 M hM).1.fg (fun y => by
      simpa only [hs] using selfDual_of_mem_genus (h1 M hM) y)
    have hγ' : γ * γ.conjTranspose = 1 := by
      rw [← hγ]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply, hs]
    refine ⟨L₀, hL₀, matEquiv γ hγ', matEquiv_mem γ hγ', ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := (matEquiv γ hγ').surjective x
    constructor
    · rintro ⟨z, hz, e⟩
      rw [← e]
      exact (hm z).1 hz
    · intro hx
      exact ⟨x, (hm x).2 hx, rfl⟩
  choose! f hf g hg hfg using key
  have hcard : s.card ≤ R.card := by
    refine Finset.card_le_card_of_injOn f (fun M hM => hf M hM) fun M hM N hN e => ?_
    have hM' : M ∈ s := hM
    have hN' : N ∈ s := hN
    refine (h2 M (h1 M hM')).unique ⟨hM', 1, one_mem _, Formalism.HermitianLatticesTheory.genusBasic_gmap_one _⟩
      ⟨hN', g M * (g N)⁻¹, mul_mem (hg M hM') (inv_mem (hg N hN')), ?_⟩
    have e1 : gmap (g N)⁻¹ N = f N := by
      conv_lhs => rw [← hfg N hN']
      rw [hfg N hN']
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (g N) (f N)
      rwa [hfg N hN'] at this
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, e1, ← e, hfg M hM']
  calc ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm E n) M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum fun M _ => Nat.cast_inv_le_one _
    _ = s.card := by simp
    _ ≤ R.card := by exact_mod_cast hcard

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecCalc

theorem smooth_calculus : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → (∀ g ∈ Formalism.QuantumDeterminants.UH J, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (π g v)) ∧ (∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ∀ c : ℂ, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (v + c • w)) ∧ ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (dRep π X v) ∧ HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH J, π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v)) ∧ (∀ c : ℝ, dRep π (c • X) v = (c : ℂ) • dRep π X v) ∧ ∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ⟪dRep π X v, w⟫_ℂ = -⟪v, dRep π X w⟫_ℂ ∧ ∀ c : ℂ, dRep π X (v + c • w) = dRep π X v + c • dRep π X w := by
  intro n H _ _ J π _ hJ hπ v hv
  have hG : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have hv' : v ∈ GlobalTheory.SmVec.smSub J π := hv
  refine ⟨fun g hg => GlobalTheory.SmVec.rep_mem hG hπ hv' hg, fun w hw c => ?_, fun X hX => ?_⟩
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    exact add_mem hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw')
  have hX' : X ∈ GlobalTheory.SmVec.lieG J := hX
  have hD := GlobalTheory.SmVec.hasDerivAt_dRep hv' hX'
  refine ⟨GlobalTheory.SmVec.dRep_mem hG hπ hv' hX', hD, fun g hg => ?_, fun c => ?_, fun w hw => ⟨?_, fun c => ?_⟩⟩
  · have hd := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
    have hY : g * X * g⁻¹ ∈ GlobalTheory.SmVec.lieG J := by
      have := GlobalTheory.SmVec.conj_mem_lieG hG (GlobalTheory.SmVec.inv_mem_UH hG hg) hX'
      rwa [Matrix.nonsing_inv_nonsing_inv _ hd] at this
    rw [GlobalTheory.SmVec.dRep_rep hG hπ hv' hg hY]
    congr 2
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  · have h1 : HasDerivAt (fun t : ℝ => t * c) c 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
    have h2 := HasDerivAt.scomp_of_eq (0 : ℝ) hD h1 (by simp)
    rw [Complex.coe_smul]
    refine Eq.trans ?_ h2.deriv
    unfold dRep
    congr 1
    funext t
    simp [Function.comp_def, smul_smul]
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    rw [GlobalTheory.SmVec.inner_dRep hG hπ hv' hw' hX', neg_neg]
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    rw [GlobalTheory.SmVec.dRep_add hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw') hX', GlobalTheory.SmVec.dRep_smul c hw' hX']

end GlobalTheory.SmVecCalc

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.PrincLevelSub

private lemma ext1_bot_one_apply {G : Type} [Group G] (x : G) :
    Formalism.L2.DIV.ext1 (⊥ : Subgroup G) (⇑(1 : (⊥ : Subgroup G) →* ℂˣ)) x = 1 := by
  unfold Formalism.L2.DIV.ext1
  split <;> rfl

theorem levChi_triv {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  simp [Lev.levChi, Formalism.L2.DIV.levFn, LevCh.datWp, LevCh.triv, Lev.datY, Formalism.L2.DIV.LevelP.triv,
    ext1_bot_one_apply]
  exact ext1_bot_one_apply _

end GlobalTheory.HolRead.PrincLevelSub
end
