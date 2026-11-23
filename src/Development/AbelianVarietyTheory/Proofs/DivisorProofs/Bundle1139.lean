module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.Bundle001
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576

@[expose] public section

section

open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.CompRestr

open GlobalTheory.FlatLine GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem idem_mem_sec (Z : Comp Xo c) : idem Z ∈ sec Xo c 0 0 := by
  rw [← secZ_nat]
  have : (fun i => (ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 i : ℤ)) = 0 := by
    funext i
    rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
  rw [this]
  exact idem_mem_secZ Z

theorem idem_mul_mem_cuspW {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (Z : Comp Xo c) {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspW Xo c U G) : idem Z * f ∈ cuspW Xo c U G := by
  rw [mem_cuspW] at hf ⊢
  refine ⟨?_, fun σ hσ => ?_⟩
  · have := mul_mem_secZ (idem_mem_secZ Z) hf.1
    rwa [zero_add] at this
  · rw [AllWt.rdU_mul]
    refine IdemCusp.mul_mem_holSub (U σ).X (modelWt (U σ) G) (rdU (U σ) (idem Z)) (fun k => ?_) (hf.2 σ hσ)
    have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
    have hs := (hU σ hσ).2.2.2.2.1 0 0 hD (idem Z) (idem_mem_sec Z) k
    have h0 : laU (U σ) 0 0 k = 0 := by
      funext τ j
      simp [laU]
    rw [h0] at hs
    refine IdemCusp.isIdemFn_of_isSec _ hs ?_
    have := congrFun (AllWt.rdU_mul (U σ) (idem Z) (idem Z)) k
    rw [idem_mul_idem] at this
    exact this.symm

theorem exists_cuspOn_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (Z : Comp Xo c) (G : WTZ E) (f : cuspW Xo c U G), ∃ g : cuspOn U Z G, (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) ∧ (f ∈ latW U G → g ∈ latOn U Z G) := by
  intro E _ _ _ H Dw l Xo c r U hU Z G f
  have hs : idem Z * (f : Rul Xo c) ∈ suppOn Z := by
    rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  refine ⟨⟨idem Z * (f : Rul Xo c), idem_mul_mem_cuspW hU Z f.2, hs⟩, fun S _ _ y hy => ?_, fun hf => ?_⟩
  · show evR Xo c (idem Z * (f : Rul Xo c)) y = evR Xo c f y
    by_cases ht : Tested y
    · have e : evR Xo c (idem Z * (f : Rul Xo c)) y = evR Xo c (idem Z) y * evR Xo c f y :=
        evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) f y
      rw [e, evR_idem hy ht, one_mul]
    · unfold evR evalAt
      rw [dite_eq_right ht, dite_eq_right ht]
  · refine (mem_supLat_iff (Z := Z) hs).2 fun la v hv => ?_
    show 0 ≤ v (idem Z * (f : Rul Xo c))
    rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
    exact hf la v (valOn_subset Z la hv)

end GlobalTheory.CompRestr
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.HorizMul

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_zpow (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (m : ℤ) (x : Frame X.Ψ r) :
    X.pnorm (m • la) (fun y => P y ^ m) x = X.pnorm la P x ^ m := by
  unfold Data.pnorm
  rw [mul_zpow, norm_zpow, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem differentiable_matDet {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Differentiable ℂ fun y : Frame Ψ r => (mat y τ).det := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

theorem horizGen_rmul' {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (x b : Frame Ψ r) :
    horizGen τ (rmul x b) = horizGen τ x * horizGen τ b := by
  show (mat x τ * mat b τ).det⁻¹ = _
  rw [Matrix.det_mul, mul_inv]
  rfl

theorem horizGen_lact' {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (γ : GL (Fin r) E) (x : Frame Ψ r) :
    horizGen τ (lact γ x) = (τ.1 γ.1.det)⁻¹ * horizGen τ x := by
  show (γ.1.map τ.1 * mat x τ).det⁻¹ = _
  rw [Matrix.det_mul, mul_inv, RingHom.map_det]
  rfl

theorem bchar_zsmul_modelFlat {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (m : ℤ) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) :
    bchar (m • modelFlat r τ) b = horizGen τ b ^ m := by
  classical
  have hd : (mat b τ).det = ∏ i, b τ i i :=
    Matrix.det_of_upperTriangular (M := mat b τ) fun a c h => (hb τ).2 a c h
  unfold bchar
  rw [Finset.prod_eq_single τ (fun τ' _ h => by simp [modelFlat, h]) (by simp)]
  simp only [Pi.smul_apply, modelFlat, if_true, smul_eq_mul, mul_neg, mul_one]
  rw [Finset.prod_zpow, horizGen, hd, inv_zpow', zpow_neg]

theorem isBddSec_horizGen_zpow (X : Data E r) (τ : X.Ψ) (m : ℤ)
    (hdet : ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) (hχ : ∀ γ ∈ X.Γ, X.χ (m • modelFlat r τ) γ = 1) :
    X.IsBddSec (m • modelFlat r τ) fun y => horizGen τ y ^ m := by
  refine ⟨⟨fun y hy => ?_, fun x _ b hb => ?_, fun γ hγ x _ => ?_⟩, Real.sqrt ‖τ.1 X.Gm.det‖ ^ m, fun y hy => ?_⟩
  · have hne : (mat y τ).det ≠ 0 := (hy τ).1
    exact (((differentiable_matDet τ y).inv hne).zpow (Or.inl (inv_ne_zero hne))).differentiableWithinAt
  · beta_reduce
    rw [horizGen_rmul', mul_zpow, bchar_zsmul_modelFlat τ m hb, mul_comm]
  · beta_reduce
    rw [horizGen_lact', hdet γ hγ, map_one, inv_one, one_mul, hχ γ hγ, one_mul]
  · rw [pnorm_zpow, pnorm_horizGen X τ hy]

theorem chi_zsmul_modelFlat (X : Data E r) (τ : X.Ψ) (la : Wt X.Ψ r) (m : ℤ)
    (hχ : ∀ γ ∈ X.Γ, X.χ (la + m • modelFlat r τ) γ = X.χ la γ) : ∀ γ ∈ X.Γ, X.χ (m • modelFlat r τ) γ = 1 := by
  intro γ hγ
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h0 : X.χ la γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h1 := (X.χ_add la (m • modelFlat r τ) γ hγ).symm.trans (hχ γ hγ)
  exact mul_left_cancel₀ h0 (h1.trans (mul_one _).symm)

theorem horizGen_zpow_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (τ : X.Ψ)
    (la : Wt X.Ψ r) (m : ℤ), (∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) →
    (∀ γ ∈ X.Γ, X.χ (la + m • modelFlat r τ) γ = X.χ la γ) →
    ∀ P ∈ X.SS la, (fun y => horizGen τ y ^ m * P y) ∈ X.SS (la + m • modelFlat r τ) := by
  intro E _ _ _ r X τ la m hdet hχ P hP
  have hQ := isBddSec_horizGen_zpow X τ m hdet (chi_zsmul_modelFlat X τ la m hχ)
  obtain ⟨hb, hfj⟩ := GlobalTheory.bddSec_mul_and_constTerm_mul E r X la _ P _ hP.1 hQ
  have e : (fun y => horizGen τ y ^ m * P y) = P * fun y => horizGen τ y ^ m := funext fun y => mul_comm _ _
  rw [e]
  refine ⟨hb, fun ξ hξ x hx => ?_⟩
  rw [hfj ξ hξ x hx, hP.2 ξ hξ x hx, zero_mul]

end GlobalTheory.FlatCore.HorizMul
end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.LFun

theorem tn_single (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (ϖ : w.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E w ϖ) :
    ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)), ∃ g,
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  classical
  intro x hx
  have h0 : ϖ ≠ 0 := Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ
  set g := Formalism.UG.P.tjcosets_dG n n ϖ h0 with hg
  have hdiag : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    unfold Formalism.UG.diagJ
    ext i j
    by_cases h : i = j
    · subst h; simp [i.2]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hcomm : ∀ a : GL (Fin n) (w.adicCompletion E), g * a = a * g := fun a => by
    ext : 1
    rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val, hdiag]
    simp
  have hT : Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n = Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL w (n := n)) g := by
    unfold Formalism.UG.Tj Formalism.UG.dosetInd
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b, hb, Units.ext (by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]; exact e)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]⟩
  refine ⟨g, ?_⟩
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx (R := {g})]
  · simp
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
    refine ⟨g, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have : g⁻¹ * (a * g * b) = a * b := by
      rw [← hcomm a]; group
    rw [this]
    exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ha hb

end GlobalTheory.LFun
end

section

namespace GlobalTheory.LFun

theorem norm_le_card_of_heckeVec_eq_smul :
    ∀ (G : Type) [Group G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) →
      (∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) → ∀ (h : G → ℂ) (x : V) (c : ℂ), (∀ g, ‖h g‖ ≤ 1) →
      {q : G ⧸ K | h q.out ≠ 0}.Finite → x ≠ 0 → GlobalTheory.LFun.heckeVec ρ K h x = c • x →
      ‖c‖ ≤ Nat.card {q : G ⧸ K // h q.out ≠ 0} := by
  intro G _ K V _ _ ρ Bf hsym hpos hinv h x c hh hfin hx hc
  classical
  have hnn : ∀ y, 0 ≤ (Bf y y).re := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (hpos y hy).le
  let core : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf x y
      conj_inner_symm := fun x y => by rw [hsym x y]; simp
      re_inner_nonneg := hnn
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have cs : ∀ y, ‖Bf x y‖ * ‖Bf y x‖ ≤ (Bf x x).re * (Bf y y).re :=
    fun y => @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ core x y
  have hr : 0 < (Bf x x).re := hpos x hx
  have hb : ∀ g, ‖Bf x (ρ g x)‖ ≤ (Bf x x).re := by
    intro g
    have h1 := cs (ρ g x)
    rw [hinv, hsym x (ρ g x), RCLike.norm_conj] at h1
    nlinarith [norm_nonneg (Bf x (ρ g x))]
  have hxx : ‖Bf x x‖ = (Bf x x).re := by
    have e : (starRingEnd ℂ) (Bf x x) = Bf x x := (hsym x x).symm
    rw [RCLike.conj_eq_iff_re] at e
    rw [← e]
    simp [abs_of_pos hr]
  set S := hfin.toFinset
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ S := by
    intro q hq
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ S, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  have key : c * Bf x x = ∑ q ∈ S, h q.out * Bf x (ρ q.out x) := by

    rw [← smul_eq_mul, ← map_smul, ← hc, hsum, map_sum]
    simp
  have hcard : Nat.card {q : G ⧸ K // h q.out ≠ 0} = S.card :=
    Nat.card_eq_card_finite_toFinset hfin
  have hle : ‖c‖ * (Bf x x).re ≤ (S.card : ℝ) * (Bf x x).re := by
    calc ‖c‖ * (Bf x x).re = ‖c * Bf x x‖ := by rw [norm_mul, hxx]
      _ = ‖∑ q ∈ S, h q.out * Bf x (ρ q.out x)‖ := by rw [key]
      _ ≤ ∑ q ∈ S, ‖h q.out * Bf x (ρ q.out x)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ S, (Bf x x).re := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul]
        calc ‖h q.out‖ * ‖Bf x (ρ q.out x)‖ ≤ 1 * (Bf x x).re :=
              mul_le_mul (hh _) (hb _) (norm_nonneg _) zero_le_one
          _ = (Bf x x).re := one_mul _
      _ = (S.card : ℝ) * (Bf x x).re := by simp
  rw [hcard]
  exact le_of_mul_le_mul_right hle hr

end GlobalTheory.LFun
end

section

open NumberField IsDedekindDomain Matrix GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc)
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.HenQ
variable {K : Type} [Field K] [NumberField K]

theorem valued_det_of_KGL {w : HeightOneSpectrum (𝓞 K)} {n : ℕ} {g : GL (Fin n) (w.adicCompletion K)}
    (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v g.val.det = 1 := by
  obtain ⟨g0, rfl⟩ := hg
  set O := (w.adicCompletionIntegers K).toSubring
  have hd : ∀ h : GL (Fin n) O, ((Formalism.UG.bc O.subtype h).val.det) = ((h.val.det : O) : w.adicCompletion K) := by
    intro h
    exact (RingHom.map_det O.subtype h.val).symm
  have h1 : Valued.v ((g0.val.det : O) : w.adicCompletion K) ≤ 1 := (g0.val.det).2
  have h2 : Valued.v (((g0⁻¹).val.det : O) : w.adicCompletion K) ≤ 1 := ((g0⁻¹).val.det).2
  have h3 : ((g0.val.det : O) : w.adicCompletion K) * (((g0⁻¹).val.det : O) : w.adicCompletion K) = 1 := by
    rw [← Subring.coe_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rfl
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  rw [hd]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h4.symm
    _ ≤ Valued.v ((g0.val.det : O) : w.adicCompletion K) * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

end GlobalTheory.HenQ
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GroundTheory.Automorphic UpperTheory.V.Af
open GlobalTheory.CuspRep (GA Af Ad pFin pLoc)

namespace GlobalTheory.HenQ.Basic

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_KGL_iff (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)) :
    y ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) ∧ ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov K w := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨fun i j => (z.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((z⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map (Formalism.UG.Ov K w).subtype = y.val := by ext i j; rfl
    have hN : N.map (Formalism.UG.Ov K w).subtype = (y⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) => A.map (Formalism.UG.Ov K w).subtype) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact hM

end GlobalTheory.HenQ.Basic
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpaceDegree

theorem topSelf_O1_str : ∀ (k : Type) [Field k] (N : ℕ),
    letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 :=
  fun k _ N => GlobalTheory.NefNumericsModel.selfIntersection_O1 k N

end GlobalTheory.ProjSpaceDegree
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M M' : LB X) (hB : B.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (s : B.Sec), Mono (cutHom F hB s) → cls M hM = cls M' hM' + cls B hB → (∀ i, hdim k (twist F M) i ≤ hdim k (twist F M') i + hdim k (twist (cut F hB s) M) i) ∧ (∀ i, hdim k (twist F M') (i + 1) ≤ hdim k (twist (cut F hB s) M) i + hdim k (twist F M) (i + 1)) ∧ hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  first | exact @GlobalTheory.hdim_twist_cut_inequalities | exact GlobalTheory.hdim_twist_cut_inequalities | (intros; apply GlobalTheory.hdim_twist_cut_inequalities <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpace

theorem lbIso_pull_O1_toProj_of_isLB : ∀ (R : Type) [CommRing R] (N : ℕ) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (f : X ⟶ Sp R) (s : Fin (N + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤), LBIso ((ProjSpace.O1 R N).pull (ProjSpace.toProj f s hs)) L :=
  fun _ _ _ _ _ _ f s hs => GlobalTheory.ProjSpace.lbIso_pullback_O1_toProj f s hs

end GlobalTheory.ProjSpace
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_matching_lineBundle_generators_near_pinching_point : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z), L'.IsLB → LZ.IsLB → ∀ w : LB.Iso (L'.pull i') (LZ.pull p'), w.IsGen → ∀ z : Z, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), i z ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ := by
  first | exact @GlobalTheory.PinchLift.near_matched | exact GlobalTheory.PinchLift.near_matched | (intros; apply GlobalTheory.PinchLift.near_matched <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors

theorem _root_.GlobalTheory.T.exists_base_globalUnit_abelianScheme_baseChange : ∀ {S X : Scheme.{0}} (A Z : Over S) [GrpObj A], IsAbelianScheme A → ∀ (p : X ⟶ A.left) (q : X ⟶ Z.left), IsPullback p q A.hom Z.hom → ∀ D : Γ(X, ⊤)ˣ, ∃ c : Γ(Z.left, ⊤)ˣ, GlobalTheory.CharKer.pullTop q c = D := by
  first | exact @GlobalTheory.CharKer.exists_pullTop_of_isPullback | exact GlobalTheory.CharKer.exists_pullTop_of_isPullback | (intros; apply GlobalTheory.CharKer.exists_pullTop_of_isPullback <;> assumption)
end
