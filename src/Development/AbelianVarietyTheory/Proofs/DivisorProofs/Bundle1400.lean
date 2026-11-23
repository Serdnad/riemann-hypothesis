module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.WhitAlg

open GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_psiNeg :
    Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)

theorem whit_eq (F : GA E a → ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit F g = ∫ X in vecDomain E (Pos a),
      F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := rfl

theorem integrableOn_whit {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) :
    IntegrableOn (fun X => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ))
      (vecDomain E (Pos a)) (vecMeasure E (Pos a)) := by
  have hcont : Continuous fun X : Pos a → Ad E => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    (hF.comp (continuous_uGL.mul continuous_const)).mul continuous_psiNeg
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whit_add_mul {F G : GA E a → ℂ} (hF : Continuous F) (hG : Continuous G) (c : ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g := by
  rw [whit_eq, whit_eq, whit_eq, ← integral_const_mul,
    ← integral_add (integrableOn_whit hF g) ((integrableOn_whit hG g).const_mul c)]
  congr 1
  funext X
  ring

theorem whit_kerInf {F : GA E a → ℂ} (hF : Continuous F)
    (hgr : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N)
    {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : GlobalTheory.JSW.IsRapidInf ν k γ) (g : GA E a) :
    GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  let ψ : (Pos a → Ad E) → ℂ := fun Y => (GroundTheory.Global.adelicChar E (-supSum 0 Y) : ℂ)
  let f : (Pos a → Ad E) → X → ℂ := fun Y x => k x * F (uGL Y * g * infGL E a (γ x)) * ψ Y
  have hmeas : Measurable (Function.uncurry f) := by
    haveI : BorelSpace ((Pos a → Ad E) × Lie E a) := Prod.borelSpace
    have hc : ContinuousOn (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) :=
      (GlobalTheory.ConstTermSmooth.continuousOn_chart hF).comp
        (((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
        fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hφ : Measurable fun p : (Pos a → Ad E) × X => ((p.1, toL (γ p.2).val) : (Pos a → Ad E) × Lie E a) :=
      measurable_fst.prodMk (hk.2.1.comp measurable_snd)
    have h1 : Measurable fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val) := by
      have e : (fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val)) =
          (Set.univ ×ˢ invSet E a).restrict (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2) ∘
            fun p => (⟨(p.1, toL (γ p.2).val), Set.mem_univ _, val_mem_invSet _⟩ :
              (Set.univ ×ˢ invSet E a : Set ((Pos a → Ad E) × Lie E a))) := rfl
      rw [e]
      exact hc.restrict.measurable.comp hφ.subtype_mk
    have e2 : Function.uncurry f = fun p => k p.2 * chart F (uGL p.1 * g) (toL (γ p.2).val) * ψ p.1 := by
      funext p
      exact congrArg (fun z => k p.2 * z * ψ p.1) (chart_val F _ _).symm
    rw [e2]
    exact ((hk.1.comp measurable_snd).mul h1).mul (continuous_psiNeg.measurable.comp measurable_fst)
  obtain ⟨C, N, hC⟩ := hgr ((fun Y => uGL Y * g) '' closure (vecDomain E (Pos a)))
    (isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const))
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    have hb : Integrable (fun p : (Pos a → Ad E) × X => (1 : ℝ) * (C * (‖k p.2‖ * height (γ p.2) ^ N))) (μ.prod ν) :=
      (integrable_const (1 : ℝ)).mul_prod ((hk.2.2 N).const_mul C)
    have hae : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ vecDomain E (Pos a) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_vecDomain)
    refine hb.mono' hmeas.aestronglyMeasurable (hae.mono fun p hp => ?_)
    have hb1 := hC (uGL p.1 * g) ⟨p.1, subset_closure hp, rfl⟩ (γ p.2)
    change ‖k p.2 * F (uGL p.1 * g * infGL E a (γ p.2)) * (GroundTheory.Global.adelicChar E (-supSum 0 p.1) : ℂ)‖ ≤ _
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    calc ‖k p.2‖ * ‖F (uGL p.1 * g * infGL E a (γ p.2))‖ ≤ ‖k p.2‖ * (C * height (γ p.2) ^ N) :=
          mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)
      _ = 1 * (C * (‖k p.2‖ * height (γ p.2) ^ N)) := by ring
  have hin : ∀ Y, GlobalTheory.JSW.kerInf ν k γ F (uGL Y * g) * ψ Y = ∫ x, f Y x ∂ν := fun Y => by
    simp only [f, GlobalTheory.JSW.kerInf]
    rw [integral_mul_const]
  calc GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ Y, ∫ x, f Y x ∂ν ∂μ := by
        rw [whit_eq]
        congr 1
        funext Y
        exact hin Y
    _ = ∫ x, ∫ Y, f Y x ∂μ ∂ν := integral_integral_swap hint
    _ = _ := by
        congr 1
        funext x
        rw [whit_eq, ← integral_const_mul]
        congr 1
        funext Y
        simp only [f, ψ, mul_assoc]

theorem whit_linear_kerInf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F G : GA E a → ℂ),
    Continuous F → Continuous G →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖G (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ (c : ℂ) (g : GA E a), GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g) ∧
      ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
        GlobalTheory.JSW.IsRapidInf ν k γ → ∀ g, GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g =
          ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  intro E _ _ _ a F G hF hG hFg _
  exact ⟨fun c g => whit_add_mul hF hG c g, fun X _ ν _ k γ hk g => whit_kerInf hF hFg ν hk g⟩

end GlobalTheory.JSW.WhitAlg
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqProd_pow_eight_mul (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ)
    (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) (hD : Datum p F L t) :
    sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  obtain ⟨hmul, -, hrep⟩ := GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD
  have ht0 : t ≠ 0 := by
    rintro rfl; exact hD.notMem (zero_mem _)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hα2 : sqrtNegNat p ^ 2 = -(p : ℂ) := by
    simp only [sqrtNegNat, mul_pow, Complex.I_sq]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    push_cast; ring
  have hα0 : sqrtNegNat p ≠ 0 := by
    intro h; apply hp0; have := hα2; rw [h] at this; simp at this; exact_mod_cast this
  have hα12 : sqrtNegNat p ^ 12 = (p : ℂ) ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, hα2]; ring
  have hinj : Set.InjOn (fun k : ℕ => (k : ℂ) * t) (Finset.Ico 1 p : Set ℕ) := by
    intro a _ b _ hab
    exact_mod_cast mul_right_cancel₀ ht0 hab
  set S := (Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t with hS
  have hcard : S.card = p - 1 := by
    rw [hS, Finset.card_image_of_injOn hinj, Nat.card_Ico]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : Even S.card := by
    rw [hcard]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
  have hpf := GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (sqrtNegNat p) S hα0 hD.mul hrep heven
  rw [hcard, hα12] at hpf
  rw [← hpf]
  congr 1

  have hprod : ∏ x ∈ S, L.derivWeierstrassP x
      = ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t) := by
    rw [hS, Finset.prod_image hinj]
  obtain ⟨e, he⟩ := GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4
  have hpt : (p : ℂ) * t ∈ L.lattice := by
    have := (hmul (p : ℤ)).2 dvd_rfl
    simpa using this
  have hsplit : ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t)
      = ∏ s : Sq p ⊕ Sq p, L.derivWeierstrassP (((e s : ℕ) : ℂ) * t) := by
    rw [← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hneg : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inr k) : ℕ) : ℂ) * t)
      = -L.derivWeierstrassP (sqPt p t k) := by
    intro k
    rw [(he k).2, Nat.cast_sub (le_of_lt k.1.2), sub_mul, sqPt]
    have := L.derivWeierstrassP_add_coe (-((k.1 : ℕ) : ℂ) * t) ⟨_, hpt⟩
    simp only at this
    rw [show (p : ℂ) * t - ((k.1 : ℕ) : ℂ) * t = -((k.1 : ℕ) : ℂ) * t + (p : ℂ) * t by ring, this,
      neg_mul, L.derivWeierstrassP_neg]
  have hpos : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inl k) : ℕ) : ℂ) * t)
      = L.derivWeierstrassP (sqPt p t k) := by
    intro k; rw [(he k).1, sqPt]
  rw [hprod, hsplit, Fintype.prod_sum_type]
  simp only [hneg, hpos, Finset.prod_neg]
  have h1 : ((-1 : ℂ) ^ (Finset.univ : Finset (Sq p)).card) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [sqProd, mul_pow, mul_pow, h1]
  ring

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.sqProd_sq_mem_and_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
    sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  intro p F L t hp h4 h3 hD
  refine ⟨?_, ?_⟩
  · apply GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F
    intro σ hσ
    rw [map_pow]
    rcases GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨h, _⟩ | h
    · rw [h]
    · rw [h, neg_sq]
  · intro hmem σ hσ
    rcases GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨_, he⟩ | h
    · exact he
    · exfalso
      have hne := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
      have hfix : σ (sqProd p L t) = sqProd p L t := hσ _ hmem
      rw [hfix] at h
      have h2 : (2 : ℂ) * sqProd p L t = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h2 | h2
      · norm_num at h2
      · exact hne h2
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.formalSquaringPaths_baseChange_and_hom : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ∧ ∀ [IsLocalRing R] (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), HasTan G b ξ τ w → ∀ (hU' : ⊤ ≤ (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)), PowerSeries.coeff 1 (evAt (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) hU' f) = ∑ i, u * φ (w i) * φ (evAt b hb (dualApp (τ i) hV (dUnit G he f)))) ∧ (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] (R : Type) [CommRing R] (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), (IsPath G c b ξ → IsPath H c b (ξ ≫ q.left)) ∧ triv G b ≫ q.left = triv H b ∧ sqr G ≫ q.left = q.left ≫ sqr H) := by
  first | exact @GlobalTheory.Nef.paths_bc | exact GlobalTheory.Nef.paths_bc | (intros; apply GlobalTheory.Nef.paths_bc <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.hasTangent_of_single_affineChart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (E : Type) [Field E] (c : E) (b : Sp E ⟶ S) (ξ : Sp (PowerSeries E) ⟶ G.left), IsPath G c b ξ → ∀ (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E) (U : G.left.Opens), IsAffineOpen U → ∀ (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V'), (∀ f : Γ(G.left, U), PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))) → HasTan G b ξ τ w := by
  first | exact @GlobalTheory.Nef.hasTan_of_affine_chart | exact GlobalTheory.Nef.hasTan_of_affine_chart | (intros; apply GlobalTheory.Nef.hasTan_of_affine_chart <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.isRationalFormalPath_of_rationalExpansions : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y), (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  first | exact @GlobalTheory.Nef.isRatPath_of_isRat | exact GlobalTheory.Nef.isRatPath_of_isRat | (intros; apply GlobalTheory.Nef.isRatPath_of_isRat <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_sectionAddition_two_point_function :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
        (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
        ∃ g : Fn2 A, IsSecAdd n S g :=
  @GlobalTheory.PtExt.exists_isSecAdd
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.detPowSection_rational_genericPoint : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ (m : ℕ) (σ : (lbPow (det W r) m).Sec), σ ≠ 0 → ∃ f : K, f ≠ 0 ∧ ∀ (v : Place k K) (g : Matrix (Fin r) (Fin r) K), LocFrame x s v g → v.1 (f * g.det ^ m) ≤ 1 ∧ ∀ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x → b (IsLocalRing.closedPoint v.O) ∉ Out.nonzeroLocus σ → v.1 (f * g.det ^ m) < 1 := by
  first | exact @GlobalTheory.Nef.sec_detPow_rational | exact GlobalTheory.Nef.sec_detPow_rational | (intros; apply GlobalTheory.Nef.sec_detPow_rational <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_stalkDerivation_of_lieSheafSections : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) (β : S.presheaf.stalk s →+* R) (n : ℕ) (V : S.Opens) (hs : s ∈ V) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), StalkData G s π ε m → ∃ δ : G.left.presheaf.stalk (unitSec G s) →+ R, (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) ∧ (∀ a, δ (π a) = 0) ∧ ∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V') (f : Γ(G.left, U)), δ (G.left.presheaf.germ U _ hU f) = ∑ i, w i * β (S.presheaf.germ V' s hs' (dualApp (τ i) hV (dUnit G he f))) := by
  first | exact @GlobalTheory.Nef.exists_stalkDer_of_lie | exact GlobalTheory.Nef.exists_stalkDer_of_lie | (intros; apply GlobalTheory.Nef.exists_stalkDer_of_lie <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.tangent_constantPath_eq_zero : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ w : Fin r → E, HasTan G (spMap (algebraMap K E) ≫ x) (triv G (spMap (algebraMap K E) ≫ x)) (fun j => i.app V₀ (s j)) w → w = 0 := by
  first | exact @GlobalTheory.Nef.tan_triv_eq_zero | exact GlobalTheory.Nef.tan_triv_eq_zero | (intros; apply GlobalTheory.Nef.tan_triv_eq_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_sectionDifference_one_cochain :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
        (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
        ∃ u : Fn1 A, IsSecDiff n S u :=
  @GlobalTheory.PtExt.exists_isSecDiff
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.groupSchemeSquaring_cotangent_eq_two : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiSeparated G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2 := by
  first | exact @GlobalTheory.Nef.sqr_sub_two_mem | exact GlobalTheory.Nef.sqr_sub_two_mem | (intros; apply GlobalTheory.Nef.sqr_sub_two_mem <;> assumption)
end
