module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.Hypotheses.GalCoh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.KerJ.RhoThree

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem norm_emb_unitary (D : D7) (φ : D.host.E →+* ℂ) (z : letI := D.host.cmStar; unitary D.host.E) :
    ‖φ (z : D.host.E)‖ = 1 := by
  let := D.host.cmStar
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have h1 : star (z : D.host.E) * (z : D.host.E) = 1 := z.2.1
  have h2 : φ (star (z : D.host.E)) = starRingEnd ℂ (φ (z : D.host.E)) :=
    IsCMField.complexEmbedding_complexConj D.host.E φ _
  have h3 : starRingEnd ℂ (φ (z : D.host.E)) * φ (z : D.host.E) = 1 := by
    rw [← h2, ← map_mul, h1, map_one]
  have h4 : ‖φ (z : D.host.E)‖ * ‖φ (z : D.host.E)‖ = 1 := by
    have := congrArg norm h3
    rwa [norm_mul, RCLike.norm_conj, norm_one] at this
  nlinarith [norm_nonneg (φ (z : D.host.E))]

theorem algebraic_modulus_one_of_finiteOrder_char (D : D7) (ρ : D.Dt →* ℂˣ) (s : D.what₂.Tau → ℤ) (t : D.Dt) (h : ℕ)
    (z : letI := D.host.cmStar; unitary D.host.E) (hp : PowRat D t h z)
    (hU : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (hz : ((ρ (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) :
    Mod1E ((ρ t : ℂˣ) : ℂ) := by
  obtain ⟨h0, k, hk, e⟩ := hp
  obtain ⟨n, hn, h1⟩ := hU k hk
  have e1 : ρ t ^ (h * n) = ρ (D.e1Dt z) ^ n := by
    rw [pow_mul, ← map_pow, e, map_mul, mul_pow, h1, mul_one]
  have e2 : ((ρ t : ℂˣ) : ℂ) ^ (h * n) = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) ^ n := by
    rw [← hz, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, e1]
  have hpos : 0 < h * n := Nat.mul_pos h0 hn
  have hw : (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) ∈ Qbar :=
    prod_mem fun τ _ => zpow_mem (embT_mem D τ _) _
  have hm : ((ρ t : ℂˣ) : ℂ) ∈ Qbar := by
    have h2 : ((ρ t : ℂˣ) : ℂ) ^ (h * n) ∈ Qbar := e2 ▸ pow_mem hw n
    exact (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h2).of_pow hpos)
  refine ⟨hm, fun r => ?_⟩
  have e3 : (⟨((ρ t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ (h * n) =
      (∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar) ^ (s τ)) ^ n := by
    apply Subtype.ext
    push_cast
    exact e2
  have h3 : ‖r ⟨((ρ t : ℂˣ) : ℂ), hm⟩‖ ^ (h * n) = 1 := by
    rw [← norm_pow, ← map_pow, e3, map_pow, map_prod, norm_pow, norm_prod]
    rw [Finset.prod_eq_one, one_pow]
    intro τ _
    have h4 := norm_emb_unitary D (r.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))) z
    rw [map_zpow₀, norm_zpow, show r ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ =
      (r.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))) (z : D.host.E) from rfl, h4, one_zpow]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 h3

theorem zpow_hom_apply {G : Type*} [CommGroup G] (f : G →* ℂˣ) (a : ℤ) (x : G) : (f ^ a) x = f x ^ a :=
  map_zpow (MonoidHom.eval x) f a

theorem half_cast (R : Ranks) (j : ℕ) : (((R.N j / 2 : ℕ) : ℤ) : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ : Even (R.N j) := R.k_even.add (R.t_odd.add_one.mul_left j)
  have h1 : R.N j / 2 = a := by omega
  rw [h1, ha]
  push_cast
  ring

theorem prod_type {ι : Type*} [Fintype ι] (x : ι → ℂ) (hx : ∀ τ, x τ ≠ 0) (e : ι → ℤ) (b c : ℤ) :
    (∏ τ, x τ ^ e τ) ^ b * (∏ τ, (x τ)⁻¹) ^ c = ∏ τ, x τ ^ (b * e τ - c) := by
  rw [← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, inv_zpow, ← zpow_neg, mul_comm (e τ) b, sub_eq_add_neg, zpow_add₀ (hx τ)]

theorem emb_ne (D : D7) (τ : D.what₂.Tau) (z : letI := D.host.cmStar; unitary D.host.E) :
    embT D τ (z : D.host.E) ≠ 0 := by
  intro h0
  have := norm_emb_unitary D (embT D τ) z
  rw [h0, norm_zero] at this
  exact zero_ne_one this

theorem rhoThreeOf_of_mtType : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ),
    MtType u mt → rhoThreeOf D C mt := by
  intro D u C mt hT i hi
  obtain ⟨hU, e, he, hz⟩ := hT i hi
  have eS : ∀ τ, C.sSharp i τ = e τ - ((D.R.N (i + 1) / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [C.sSharp_eq i hi τ, Int.cast_sub, he τ, half_cast]
    simp only [sExp']
  have eD : ∀ τ, C.sDiv i τ = e τ - ((D.R.N i / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [C.sDiv_eq i hi τ, Int.cast_sub, he τ, half_cast]
    simp only [sExp, Nat.add_sub_cancel]
  have hk : ∀ k ∈ D.UO, rhoOf D mt i k = (mt (i + 1) k)⁻¹ ∧ rhoOf' D mt i k = mt (i + 1) k := fun k hk => by
    constructor
    · simp [rhoOf, zpow_hom_apply, D.chiD_UO k hk]
    · simp [rhoOf', zpow_hom_apply, D.chiD_UO k hk]
  have hV : ∀ z : (letI := D.host.cmStar; unitary D.host.E),
      ((rhoOf D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (-C.sSharp i τ) ∧
      ((rhoOf' D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (C.sDiv i τ) := fun z => by
    have hc : ((D.chiD (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E))⁻¹ := D.rest_detCharacter_on_unitary_eq z
    constructor
    · have h1 := prod_type (fun τ => embT D τ (z : D.host.E)) (fun τ => emb_ne D τ z) e (-1)
        (-((D.R.N (i + 1) / 2 : ℕ) : ℤ))
      simp only [rhoOf, MonoidHom.mul_apply, zpow_hom_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, MonoidHom.inv_apply,
        Units.val_inv_eq_inv_val, hc, hz z]
      rw [← zpow_neg_one, h1]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [eS τ]
      congr 1
      ring
    · have h1 := prod_type (fun τ => embT D τ (z : D.host.E)) (fun τ => emb_ne D τ z) e 1
        (((D.R.N i / 2 : ℕ) : ℤ))
      simp only [rhoOf', MonoidHom.mul_apply, zpow_hom_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, hc, hz z]
      rw [← zpow_one (∏ τ, embT D τ (z : D.host.E) ^ e τ), h1]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [eD τ]
      congr 1
      ring
  have hU1 : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf D mt i k ^ n = 1 := fun k hk' => by
    obtain ⟨n, hn, h1⟩ := hU k hk'
    exact ⟨n, hn, by rw [(hk k hk').1, inv_pow, h1, inv_one]⟩
  have hU2 : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf' D mt i k ^ n = 1 := fun k hk' => by
    obtain ⟨n, hn, h1⟩ := hU k hk'
    exact ⟨n, hn, by rw [(hk k hk').2, h1]⟩
  refine ⟨fun t h z hp => ⟨algebraic_modulus_one_of_finiteOrder_char D _ _ t h z hp hU1 (hV z).1, algebraic_modulus_one_of_finiteOrder_char D _ _ t h z hp hU2 (hV z).2⟩, fun k hk' => ?_, hV⟩
  obtain ⟨n, hn, h1⟩ := hU k hk'
  exact ⟨n, hn, by rw [(hk k hk').1, inv_pow, h1, inv_one], by rw [(hk k hk').2, h1]⟩

end GlobalTheory.KerJ.RhoThree
end
end

section

noncomputable section

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem normV_pos (w : PlE H) : 0 < normV w := by
  have h := GlobalTheory.LocalInv.one_lt_normV w
  have : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by linarith
  exact_mod_cast this

theorem frob_one {w : PlE H} {a : A.LP w} (hu : A.unr a) (hd : A.lpDim a = 1) : ∃ c, A.frobEig a = {c} :=
  Multiset.card_eq_one.1 (by rw [A.frobEig_card a hu, hd])

theorem eta_frob (hAut : At.TieAut N A) (w : PlE H) : ∃ b, A.frobEig (A.locG A.etaT w) = {b} ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := frob_one (A.etaT_unr w) (A.locG_dim A.etaT w)
  refine ⟨b, hb, (A.tempered_unr _ (A.etaT_unr w)).1 (hAut.2.2.1 w) b ?_⟩
  rw [hb]
  exact Multiset.mem_singleton_self b

theorem norm_first_character_frobenius (hAut : At.TieAut N A) (i : N.Loc) {w : PlE H} (hw : SplitOut N i w)
    (huμ : A.unr (A.locG (A.muC i) w)) {B : ValuationSubring N.Om} {σ : G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    ‖A.iotaQC i (iotaOQ N A i (chi1 N i σ))‖ =
      (normV w : ℝ) ^ (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2) := by
  obtain ⟨hu, hf⟩ := A.chi_mu i w hw
  have e : A.frobEig (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2)) =
      {A.iotaQC i (iotaOQ N A i (chi1 N i σ))} := hf B σ hB hσ
  rw [A.frobEig_tw _ _ hu, A.locG_tw] at e
  obtain ⟨m, hm⟩ := frob_one huμ (A.locG_dim (A.muC i) w)
  have hm1 : ‖m‖ = 1 := (A.tempered_unr _ huμ).1 (hAut.2.2.2 i w) m (by rw [hm]; exact Multiset.mem_singleton_self m)
  obtain ⟨b, hb, hb1⟩ := eta_frob hAut w
  obtain ⟨hui, hfi⟩ := A.etaTinv_def w
  have hfi' : A.frobEig (A.locG A.etaTinv w) = {b⁻¹} := by rw [hfi, hb, Multiset.map_singleton]
  have hfe := A.frobEig_char (A.locG (A.muC i) w) (A.locG A.etaTinv w) b⁻¹ huμ hui (A.locG_dim _ w) hfi'
  rw [hfe, hm, Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at e
  rw [← e, norm_mul, norm_mul, hm1, norm_inv, hb1, inv_one, one_mul, one_mul,
    Complex.norm_natCast_cpow_of_pos (normV_pos w), Complex.ofReal_re]

theorem eps_frob (i : N.Loc) {w : PlE H} (hl : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    A.iotaQC i (iotaOQ N A i ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i)) = (normV w : ℂ) := by
  have hc := cycZ_of_isFrob (F := H.E) (Ω := N.Om) (l := N.l i) (by simpa [placesOver] using hl) hB hσ
  have e1 : ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [e1, hc]
  show A.iotaQC i (A.iotaQ i (algebraMap (N.O i) (FractionRing (N.O i))
    (algebraMap ℤ_[N.l i] (N.O i) ((normV w : ℕ) : ℤ_[N.l i])))) = _
  rw [A.iotaQ_alg i, PadicInt.coe_natCast, map_natCast, map_natCast]

end GlobalTheory.FrobeniusCharacterNorms

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

end GlobalTheory.FrobeniusCharacterNorms
end
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem alternatingWord_numerical_bounds :
    ∀ (l : ℕ) (B η S M b : ℝ), 11 ≤ l → 100 ≤ B → 0 ≤ η → 0 ≤ S → 2 * η + S ≤ B / 10 →
      |M - B| ≤ η → |b - B| ≤ η → (M + S) / 2 ≤ b ∧
      2 * ((M + S + η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + (Real.logb l (2 * (M + S + η)) + 1))
        + η + 1 ≤ b := by
  intro l B η S M b hl hB hη hS hBS hM hb
  have hl' : (11:ℝ) ≤ l := by exact_mod_cast hl
  rw [abs_le] at hM hb
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨by linarith, ?_⟩
  have hx1 : M + S + η ≤ 11/10 * B := by linarith
  have hx0 : 100 ≤ M + S + η := by linarith
  have hfrac : (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 ≤ 21/100 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hfrac0 : 0 ≤ (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  have h1 : (M + S + η) * (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 ≤ 231/1000 * B := by
    rw [mul_div_assoc]
    nlinarith [mul_le_mul_of_nonneg_left hfrac (show 0 ≤ M + S + η by linarith),
      mul_le_mul_of_nonneg_right hx1 hfrac0]
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog100 : Real.log 100 < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have he : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (100:ℝ) < 2.7182818283 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
  have hlogy : Real.log (2 * (M + S + η)) ≤ 2 * (M + S + η) / 100 - 1 + Real.log 100 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * (M + S + η) / 100 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    linarith
  have hlogb : Real.logb l (2 * (M + S + η)) ≤ 2 * (M + S + η) / 100 + 4 := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have : 0 ≤ Real.log (2 * (M + S + η)) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlogl (show 0 ≤ 2 * (M + S + η) / 100 + 4 by linarith)]
  linarith

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.MuCharProof

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) :
    M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

theorem mem_list_sum {α β : Type} (L : List α) (f : α → Multiset β) {a : α} (ha : a ∈ L) {b : β}
    (hb : b ∈ f a) : b ∈ (L.map f).sum :=
  Multiset.mem_of_le (List.le_sum_of_mem (List.mem_map_of_mem ha)) hb

end GlobalTheory.MuCharProof
end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory

theorem primitiveRoot_notPrimePow_map_ne_one :
    ∀ (k : Type) [Field k] (O : Type) [CommRing O] [IsDomain O] (f : O →+* k) (ζ : O) (n : ℕ),
      1 < n → IsPrimitiveRoot ζ n → (¬ IsPrimePow n) → f ζ ≠ 1 := by
  intro k _ O _ _ f ζ n hn hζ hpp h1
  have hroot : IsRoot (cyclotomic n O) ζ := hζ.isRoot_cyclotomic (by omega)
  have h0 : eval (f ζ) (cyclotomic n k) = 0 := by
    rw [← map_cyclotomic n f, eval_map, eval₂_at_apply, hroot.eq_zero, map_zero]
  have hone : eval (1 : k) (cyclotomic n k) = 1 := by
    apply eval_one_cyclotomic_not_prime_pow
    intro p hp j hj
    exact hpp (hj ▸ (Nat.Prime.isPrimePow hp).pow (by rintro rfl; simp at hj; omega))
  rw [h1, hone] at h0
  exact one_ne_zero h0

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.StringRepresentationDecomposition

theorem cycMod_eq_one_of_mem_Ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cycMod F Ω l r σ = 1 := by
  apply Units.ext
  have e := cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) r
  simp only [Nat.cast_one, map_one] at e
  simpa [cycMod] using e

theorem tame_vanish : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ContAction rho → (∃ γ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A ∧ Function.Bijective fun m : M => rho γ m - m) → H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  intro _ hTD hEC F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v rho hA hl hrho hex
  obtain ⟨γ, hγI, hγ⟩ := hex

  have h0 : H0 rho = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro m hm
    have h1 : rho γ m = m := (Representation.mem_invariants rho m).mp hm γ
    apply hγ.1
    show rho γ m - m = rho γ 0 - 0
    rw [h1, map_zero, sub_self, sub_self]

  set χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype with hχdef
  have hχ : χ γ = 1 := cycMod_eq_one_of_mem_Ine 1 hl hA hγI
  have hdual : Subsingleton (H0 ((twDual χ rho).comp (MonoidHom.id _))) := by
    have key : ∀ φ ∈ H0 ((twDual χ rho).comp (MonoidHom.id _)), φ = 0 := by
      intro φ hφ
      have h1 : twDual χ rho γ φ = φ := (Representation.mem_invariants _ φ).mp hφ γ
      apply DFunLike.ext
      intro x
      obtain ⟨m, rfl⟩ := hγ.2 x
      have h3 := congrArg (fun ψ : TDual (ZMod (l ^ 1)) M => ψ (rho γ m)) h1
      simp only [twDual_apply, hχ, Units.val_one, one_mul] at h3
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h3
      show φ (rho γ m - m) = 0
      exact (LinearMap.map_sub (φ : Module.Dual (ZMod (l ^ 1)) M) (rho γ m) m).trans (sub_eq_zero.mpr h3.symm)
    refine ⟨fun a b => ?_⟩
    exact Subtype.ext ((key a.1 a.2).trans (key b.1 b.2).symm)

  have hTD' := hTD F Ω l 1 M A rho v Nat.one_pos hA hrho
  have hinj := hTD'.2.2.2.2.1
  have h2 : Subsingleton (H2 rho) := by
    refine ⟨fun x y => hinj ?_⟩
    ext z
    rw [Subsingleton.elim z 0, map_zero, map_zero]

  have hc0 : Nat.card (H0 rho) = 1 := by
    rw [h0]; exact Nat.card_unique
  have hc2 : Nat.card (H2 rho) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩
  have he := (hEC F Ω l 1 M A rho v Nat.one_pos hA hrho).2 hl
  have hc1 : Nat.card (H1 rho) = 1 := by rw [he, hc0, hc2]
  exact ⟨h0, (Nat.card_eq_one_iff_unique.mp hc1).1, h2⟩

end GlobalTheory.StringRepresentationDecomposition
end
end
