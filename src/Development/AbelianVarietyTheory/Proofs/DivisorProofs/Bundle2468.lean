module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SmallScal



theorem exists_small_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (n : ℕ) (La : GenLat E n), La.Unimod → ∃ s : c.F, s ≠ 0 ∧ Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c La.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ ∧ ∀ σ : c.F →+* ℂ, ‖σ s‖ ^ 2 * ((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) ≤ Real.exp (fieldSz c.F) ^ 2 := by
  intro E _ _ _ H Dw l c n La hU
  haveI : IsTotallyComplex c.F := GlobalTheory.CompHS.isTotallyComplex_coeff c
  obtain ⟨𝔞, h0, h1, h2⟩ := GlobalTheory.BetaEx.exists_index_ideal La.Ln La.La inf_le_left
    (GlobalTheory.BetaEx.bdd_of_unimod La hU) (fun m hm => by
      obtain ⟨a, ha, h⟩ := GlobalTheory.BetaEx.exists_smul_std m
      exact ⟨a, ha, La.La.smul_mem a hm, h⟩)
  set idx : ℕ := (La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index with hidx
  have h2' : Ideal.absNorm 𝔞 = idx := h2
  have hidx0 : idx ≠ 0 := by
    rw [← h2']; exact fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)

  have e : ∀ τ, idealAt c La.Ln τ =
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c La.La τ := by
    intro τ
    unfold idealAt
    rw [← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.Ln),
      ← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.La)]
    have := GlobalTheory.BetaEx.span_image_smul (embF c τ) 𝔞 (GlobalTheory.BetaEx.detSpan La.La)
    rw [← h1] at this
    exact this
  let φ : (E →+* ℂ) → (𝓞 E →+* 𝓞 c.F) := fun τ => RingOfIntegers.mapRingHom (embF c τ)
  let B : FractionalIdeal (𝓞 c.F)⁰ c.F :=
    ∏ τ : E →+* ℂ, ((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) ^ Dw.mult τ

  have hS : ∀ τ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ≤
      (((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) := by
    intro τ
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨φ τ a, Ideal.mem_map_of_mem _ ha, rfl⟩
  have hSB : ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ≤
      (B : Submodule (𝓞 c.F) c.F) := by
    have : (B : Submodule (𝓞 c.F) c.F) = FractionalIdeal.coeSubmoduleHom (𝓞 c.F)⁰ c.F B := rfl
    rw [this, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_pow]
    exact pow_le_pow_left' (hS τ) _

  obtain ⟨k, hk⟩ : ∃ k, k = InfinitePlace.nrComplexPlaces c.F := ⟨_, rfl⟩
  have hnF : Module.finrank ℚ c.F = 2 * k := hk ▸ IsTotallyComplex.finrank c.F
  have hnE : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have hk0 : k ≠ 0 := by have := Module.finrank_pos (R := ℚ) (M := c.F); omega
  have hdvd : Module.finrank ℚ E ∣ Module.finrank ℚ c.F :=
    (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ (Classical.arbitrary _)) 𝔞).1
  have hexp : Module.finrank ℚ c.F / Module.finrank ℚ E * ∑ τ : E →+* ℂ, Dw.mult τ = (Dw.p + Dw.q) * k := by
    rw [GlobalTheory.RefSum.sum_mult]
    obtain ⟨t, ht⟩ := hdvd
    have hE0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    rw [ht, Nat.mul_div_cancel_left _ hE0, hnE, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [ht, hnE] at hnF
    have : InfinitePlace.nrComplexPlaces E * t = k := by linarith
    rw [← this]; ring
  have hNB : FractionalIdeal.absNorm B = ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k := by
    simp only [B, map_prod, map_pow, FractionalIdeal.coeIdeal_absNorm]
    simp only [fun τ => (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ τ) 𝔞).2, h2']
    rw [← pow_mul, ← hexp, pow_mul, Finset.prod_pow_eq_pow_sum]
    push_cast
    ring
  have hX0 : (0 : ℝ) < (idx : ℝ) ^ (Dw.p + Dw.q) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hidx0) _
  have hB0 : B ≠ 0 := by
    intro hB
    have := hNB
    rw [hB, map_zero] at this
    have h' : ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hidx0))
    exact h' this.symm

  set X : ℝ := (idx : ℝ) ^ (Dw.p + Dw.q) with hXdef
  set R : ℝ := Real.exp (fieldSz c.F) ^ 2 with hR
  have hR0 : 0 < R := by positivity
  have hg : 0 < R / X := div_pos hR0 hX0
  have hcard : Fintype.card (InfinitePlace c.F) = k := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hk]
  have hd1 : (1 : ℝ) ≤ |(discr c.F : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero c.F)
    exact_mod_cast this
  have hdR : |(discr c.F : ℝ)| ≤ R ^ k := by
    rw [hR, ← pow_mul, ← Real.exp_nat_mul, ← Real.exp_log (lt_of_lt_of_le one_pos hd1)]
    apply Real.exp_le_exp.2
    have hn : (0 : ℝ) < Module.finrank ℚ c.F := by exact_mod_cast Module.finrank_pos
    have hfs := GlobalTheory.CovTop.log_rd_le_fieldSz c.F
    have hlog := Real.log_natCast_nonneg (Module.finrank ℚ c.F)
    have : Real.log |(discr c.F : ℝ)| ≤ (Module.finrank ℚ c.F : ℝ) * fieldSz c.F := by
      rw [div_le_iff₀ hn] at hfs; linarith
    rw [hnF] at this
    push_cast at this ⊢
    linarith
  have hsq : Real.sqrt |(discr c.F : ℝ)| ≤ |(discr c.F : ℝ)| :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hsq0 : 0 < Real.sqrt |(discr c.F : ℝ)| := Real.sqrt_pos.2 (by linarith)
  obtain ⟨b, hb, hb0, hbw⟩ := Formalism.ExtensionFiltration.mk_lt c.F (Units.mk0 B⁻¹ (inv_ne_zero hB0))
    (fun _ => Real.sqrt (R / X)) (fun _ => Real.sqrt_pos.2 hg) (by
      rw [Units.val_mk0, map_inv₀, hNB, Finset.prod_const, Finset.card_univ, hcard, Real.sq_sqrt hg.le, ← hk,
        div_pow]
      push_cast
      rw [← hXdef]
      have hXk : 0 < X ^ k := pow_pos hX0 k
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_lt_iff₀ hXk, mul_div_assoc', div_mul_cancel₀ _ hXk.ne']
      calc (2 : ℝ) ^ k * Real.sqrt |(discr c.F : ℝ)| < Real.pi ^ k * Real.sqrt |(discr c.F : ℝ)| :=
            mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) hk0) hsq0
        _ ≤ Real.pi ^ k * R ^ k := by gcongr; exact hsq.trans hdR)
  refine ⟨b, hb0, ?_, fun σ => ?_⟩
  ·
    have hsb : Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F) ≤ 1 := by
      have h1' : Submodule.span (𝓞 c.F) {b} ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) :=
        Submodule.span_le.2 (Set.singleton_subset_iff.2 hb)
      calc Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F)
          ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) * (B : Submodule (𝓞 c.F) c.F) :=
            mul_le_mul' h1' le_rfl
        _ = 1 := by rw [← FractionalIdeal.coe_mul, inv_mul_cancel₀ hB0, FractionalIdeal.coe_one]
    simp only [e, mul_pow, Finset.prod_mul_distrib]
    rw [← mul_assoc]
    calc Submodule.span (𝓞 c.F) {b} * (∏ τ : E →+* ℂ,
            Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ) *
            ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ
        ≤ 1 * ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ :=
          mul_le_mul' ((mul_le_mul' le_rfl hSB).trans hsb) le_rfl
      _ = _ := one_mul _
  ·
    have h1 := hbw (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h1
    have h3 : ‖σ b‖ ^ 2 < R / X := (Real.lt_sqrt (norm_nonneg _)).1 h1
    rw [lt_div_iff₀ hX0] at h3
    exact h3.le

end GlobalTheory.SmallScal
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HSApp

section Gen

open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}


set_option maxHeartbeats 2000000 in
theorem exists_semilinear_L2_independent (hS : Out.SecBaseChangeSt) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (V : HSp D)
    (dict : Formalism.L2.Theta.GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : Formalism.L2.Theta.GA D V → ℂ)
    (hmu1 : ∀ g, ‖mu g‖ = 1) (hm : Formalism.L2.Pj.AdelMeas U σ V dict mu) (hae : Formalism.L2.Pj.AeDom U σ V dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hunit : ∀ g τ i, ‖dmin ((U σ).X (dict g).1).Gm (dict g).2 τ i‖ = 1) (G : WTZ E) (x : ℝ) :
    ∃ Φ : GlobalTheory.AllWt.cuspW Xo c U G →+ Lp ℂ 2 (muQ1 V), (∀ (a : c.F) f, Φ (a • f) = σ a • Φ f) ∧
      (∀ f : GlobalTheory.AllWt.cuspW Xo c U G, GlobalTheory.AllWt.petAt (U σ) x V dict (muQ1 V) G (f : Rul Xo c) = ‖Φ f‖) ∧
      ∀ (n : ℕ) (e : Fin n → GlobalTheory.AllWt.cuspW Xo c U G), LinearIndependent c.F e →
        LinearIndependent ℂ (fun i => Φ (e i)) := by
  have hhol : ∀ f : GlobalTheory.AllWt.cuspW Xo c U G,
      rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f =>
    (GlobalTheory.AllWt.mem_cuspW.1 f.2).2 σ hσ
  have heq : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      eLpNorm (onQ V (adel V dict mu P)) 2 (muQ1 V) =
        GlobalTheory.AllWt.petE V dict (muQ1 V) (GlobalTheory.AllWt.modelWt (U σ) G) P := by
    intro P
    unfold GlobalTheory.AllWt.petE
    have hp : ∀ q : AutQ V, ‖mu q.out * (P : FDSec (U σ).X) (dict q.out).1 (dict q.out).2‖ =
        GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt (U σ) G) P (dict q.out) := by
      intro q
      rw [norm_mul, hmu1, one_mul, GlobalTheory.AllWt.ptN,
        pnorm_eq_of_unit _ _ _ _ (hunit q.out)]
    have hf := aesm_of_holSub hm _ P.2
    have hg := hf.norm.congr (Filter.Eventually.of_forall hp)
    have hh := eLpNorm_congr_norm_ae (p := 2) hf hg (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (GlobalTheory.AllWt.ptN_nonneg _ _ _)]
      exact hp q)
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hg] at hh
    simpa using hh
  have hmem : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      MemLp (onQ V (adel V dict mu (P : FDSec (U σ).X))) 2 (muQ1 V) := fun P =>
    by
      change eLpNorm _ _ _ < ⊤
      rw [heq P]
      exact lt_top_iff_ne_top.2 (GlobalTheory.AllWt.petE_ne_top V dict (muQ1 V) prob_le_one hd P.2)
  let L : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) →ₗ[ℂ] Lp ℂ 2 (muQ1 V) :=
    { toFun := fun P => (hmem P).toLp _
      map_add' := fun P Q => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_add, map_add (f := _), map_add (f := _)]))
      map_smul' := fun a P => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_smul, map_smul, map_smul])) }
  have hL : ∀ P, L P = (hmem P).toLp _ := fun _ => rfl
  let R : GlobalTheory.AllWt.cuspW Xo c U G → holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f => ⟨_, hhol f⟩
  have hRadd : ∀ f g, R (f + g) = R f + R g := fun f g => Subtype.ext (by
    show rdU (U σ) ((f + g : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = rdU (U σ) (f : Rul Xo c) + rdU (U σ) (g : Rul Xo c)
    rw [Submodule.coe_add, map_add (f := _)])
  have hRsm : ∀ (a : c.F) f, R (a • f) = σ a • R f := fun a f => Subtype.ext (by
    show rdU (U σ) ((a • f : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = σ a • rdU (U σ) (f : Rul Xo c)
    rw [Submodule.coe_smul, map_smulₛₗ])
  let cf : ℝ := GlobalTheory.AllWt.lieFacZ Dw x G
  have hcf : 0 < cf := GlobalTheory.AllWt.lieFacZ_pos x G
  refine ⟨AddMonoidHom.mk' (fun f => (cf : ℂ) • L (R f)) (fun f g => by rw [hRadd, map_add (f := _), smul_add]),
    fun a f => ?_, fun f => ?_, fun n e he => ?_⟩
  · show (cf : ℂ) • L (R (a • f)) = σ a • ((cf : ℂ) • L (R f))
    rw [hRsm, map_smul, smul_comm]
  · show _ = ‖(cf : ℂ) • L (R f)‖
    rw [norm_smul, hL, Lp.norm_toLp, heq, Complex.norm_real, Real.norm_of_nonneg hcf.le]
    rfl
  · have hb : LinearIndependent c.F (fun i => (e i : Rul Xo c)) :=
      he.map' (GlobalTheory.AllWt.cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := GlobalTheory.reading_linearIndependent_secZ hS (U σ) hU _ n _
      (fun i => GlobalTheory.AllWt.cuspW_le_secZ G (e i).2) hb
    rw [Fintype.linearIndependent_iff] at hc ⊢
    intro w hw
    refine hc w ?_
    have h1 : (cf : ℂ) • L (∑ i, w i • R (e i)) = 0 := by
      have hw' : ∑ i, w i • ((cf : ℂ) • L (R (e i))) = 0 := hw
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum, ← hw']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [L.map_smul]
      exact smul_comm _ _ _
    have h2 : L (∑ i, w i • R (e i)) = 0 :=
      (smul_eq_zero.1 h1).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')
    have h3 : onQ V (adel V dict mu ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) :
        FDSec (U σ).X)) =ᵐ[muQ1 V] 0 := by
      refine (MemLp.coeFn_toLp (hmem _)).symm.trans ?_
      rw [← hL, h2]
      exact Lp.coeFn_zero _ _ _
    have h4 := hae _ _ (∑ i, w i • R (e i)).2 h3
    have h5 : ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) : FDSec (U σ).X) =
        ∑ i, w i • rdU (U σ) (e i : Rul Xo c) := by
      rw [Submodule.coe_sum]
      rfl
    rw [h5] at h4
    funext k z
    by_cases hz : z ∈ ((U σ).X k).dom
    · exact h4 k z hz
    · simp [Finset.sum_apply, rdU, hz]

end Gen


set_option maxHeartbeats 2000000 in
theorem hasGram_nrm_of_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (G : WTZ D.host.E) : GlobalTheory.AllWt.HasGram (Y.nrm G) := by
  haveI := GlobalTheory.Deep.finiteDimensional_V_of_good D T j Y e o hY G
  refine GlobalTheory.HSApp.hasGram_of_inner Y.d.c₂.F (Y.V G) (Y.nrm G) fun v => ?_
  have hσ' : GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) := Formalism.L2.Pj.goodEmb_goodOf _ _
  have hd : ∀ g, (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).2 ∈
      ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).1).dom :=
    fun g => ((hY.dictU _ hσ').choose_spec.choose_spec.2).2.2.2.1 g
  have hex := exists_semilinear_L2_independent GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ' (hY.unf _ hσ')
    (D.sp.W j) (Y.dict _) (fun _ => (1 : ℂ)) (fun _ => norm_one)
    (GlobalTheory.CovTop.PetRep.adelMeas_one_of_good Y hY _ hσ') (GlobalTheory.PetDef.aeDom_good Y hY _ hσ') hd (hY.unit _ hσ') G (xiR D)
  refine ⟨_, inferInstance, inferInstance, Classical.choose hex, ?_, fun x => (Classical.choose_spec hex).2.1 x,
    (Classical.choose_spec hex).2.2⟩
  by_cases h : GoodEmb Y.d.c₂ v.embedding
  · left
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (if_pos h))
  · right
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (if_neg h))


end GlobalTheory.HSApp
end
end

section

namespace GlobalTheory.HodgeMultNum

theorem nat_bound (r f T : ℕ) (hr : 100 ≤ r) (hf : 5 ≤ f) (hT : 11 * (f * r.choose 2) ^ 2 ≤ T) :
    2 * r + 50 * r ^ 2 * (f * (r * r / 4)) + 2 ≤ T := by
  have hq : 4 * (r * r / 4) ≤ r * r := Nat.mul_div_le (r * r) 4
  have hc : 2 * r.choose 2 = r * (r - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 100 := ⟨r - 100, by omega⟩
  have h1 : s + 100 - 1 = s + 99 := by omega
  rw [h1] at hc
  set q := (s + 100) * (s + 100) / 4
  set c := (s + 100).choose 2
  have key : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) ≤ 4 * (11 * (f * c) ^ 2) := by
    have e1 : 4 * (11 * (f * c) ^ 2) = 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by rw [← hc]; ring
    rw [e1]
    have e2 : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) = 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * (4 * q) := by ring
    rw [e2]
    have h3 : 50 * (s+100)^2 * f * (4 * q) ≤ 50 * (s+100)^2 * f * ((s+100)*(s+100)) := Nat.mul_le_mul_left _ hq
    have h4 : 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * ((s+100)*(s+100)) ≤ 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      ring_nf
      nlinarith [Nat.zero_le (s * g), Nat.zero_le (s * g ^ 2), Nat.zero_le (s ^ 2 * g), Nat.zero_le (s ^ 2 * g ^ 2),
        Nat.zero_le (s ^ 3 * g), Nat.zero_le (s ^ 3 * g ^ 2), Nat.zero_le (s ^ 4 * g), Nat.zero_le (s ^ 4 * g ^ 2),
        Nat.zero_le (s ^ 2), Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 4), Nat.zero_le (g ^ 2)]
    omega
  omega

theorem five_le_of_pow (r f : ℕ) (hr : 100 ≤ r) (h : (r : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ 1 / 16) : 5 ≤ f := by
  by_contra hf
  push_neg at hf
  have h1 : (7 / 8 : ℝ) ^ 4 ≤ (7 / 8 : ℝ) ^ f := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (100 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [pow_pos (show (0:ℝ) < 7/8 by norm_num) f]

end GlobalTheory.HodgeMultNum

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

theorem GlobalTheory.HodgeMultNum.hodgeMult_le_TO : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x →
    ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤
      (Fm.parT x hx ι).TO := by
  refine Closed.imp GlobalTheory.T.badShareSize_bounds_along_family fun Fm _ _ H => ?_
  obtain ⟨x0, H⟩ := H
  refine ⟨x0, fun x hx h0 ι => ?_⟩
  obtain ⟨hr, -, hE, hk⟩ := H x hx h0 ι
  obtain ⟨hg, hsum⟩ := hk 0
  set D := Fm.D x ι
  set g : ℝ := (D.host.g 0 : ℝ)
  have hg1 : (4096 : ℝ) ≤ g := by simp only [g]; exact_mod_cast hg
  have hlogg : 0 ≤ Real.log g := Real.log_nonneg (by linarith)
  have hr' : (100 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hr
  have hlogr : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg (by linarith)
  have hfpos : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hmpos : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ 3 * (D.R.f : ℝ) / g := by positivity
  have hB : 0 ≤ 23 * (D.R.f : ℝ) * Real.log g / Real.sqrt g := by positivity
  have hC : 0 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) +
      (1 + Real.log (D.R.r : ℝ)) / (g - 1)) := by
    have : 0 ≤ g - 1 := by linarith
    positivity
  have hE' : 0 ≤ Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := (Real.exp_pos _).le
  have hP : (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f ≤ 1 / 16 := by linarith
  have hf := GlobalTheory.HodgeMultNum.five_le_of_pow _ _ hr hP
  have hT := (Fm.parT x hx ι).TO_11D2
  rw [(Fm.parT x hx ι).Dp_eq] at hT
  exact GlobalTheory.HodgeMultNum.nat_bound _ _ _ hr hf hT
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.KSplit.om_linW_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c ι hι g hg h hh φ hφ φ₁ hφ₁ hA
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hp v
  have oneX : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ X.J) - 1) = 0
    simp [mat]
  have oneW : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  have hspl := hp.weil.isUSplitting
  obtain ⟨φ', ⟨hφ', hA'⟩, -⟩ := hex 1 oneX h hh φ hφ
  obtain ⟨φ'', ⟨hφ'', hA''⟩, -⟩ := hex g hg 1 oneW φ' hφ'
  have hcomp : Acts (evFin F v) (om (g, h)) φ φ'' := by
    intro R hR
    have e : om (g, h) = om (g, 1) * om (1, h) := by rw [← map_mul]; simp
    have hR' : Rest (evFin F v) φ' R := ⟨hR.1, by rw [← hA' R hR]; exact hspl.pres (1, h) _ hR.2⟩
    rw [e, Module.End.mul_apply, hA' R hR, hA'' R hR']
  have e1 : φ₁ = φ'' := (hex g hg h hh φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ'', hcomp⟩
  obtain ⟨κW, hW⟩ := GlobalTheory.T.linear_model_unitary_conjugate hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  obtain ⟨κX, hX⟩ := GlobalTheory.T.linear_model_compact_conjugate_exists hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  have sW := GlobalTheory.T.linear_model_compact_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κW hW h hh
  have sX := GlobalTheory.T.linear_model_unitary_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κX hX g hg
  rw [e1, hX g hg φ' hφ' φ'' hφ'' hA'', hW h hh φ hφ φ' hφ' hA', sW, sX]
  funext Y
  simp only [GlobalTheory.SplitFlip.omA, Pi.smul_apply, smul_eq_mul, Fintype.card_fin, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, inv_inv, Matrix.mul_assoc]
  ring
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.deRham_degree_one_class_pullback_of_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z1) (k' : (KK D'.κ D'.t).Z1) (w : cechDeRhamTotalCocyclesOne (OAff D.s)) (w' : cechDeRhamTotalCocyclesOne (OAff D'.s)), Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k.1) w.1 → Λ'.Res1 (((KK D'.κ D'.t).resMap Λ'.L).p1 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D0 g = ((pairB Λ' φ m).pre θ).p1 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1 → IsPull1 hφ (Hyp1.mk _ w) (Hyp1.mk _ w') := by
  first | exact @GlobalTheory.PDForm.isPull1_of_pair_coboundary | exact GlobalTheory.PDForm.isPull1_of_pair_coboundary | (intros; apply GlobalTheory.PDForm.isPull1_of_pair_coboundary <;> assumption)
end
