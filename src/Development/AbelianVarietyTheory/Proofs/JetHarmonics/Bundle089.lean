module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddFirstSecond
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddSecondThird
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle018
public import Formalism.UnipotentAdelicQuotients.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsoMultiplicative
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle007

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart dLin)

namespace GlobalTheory.GaugeShift

open ReciprocityTheory.ChartRestriction.G.TB.LogPf (CZ ev_sub ev_zeroFam logOf)
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix (bilL lg)
open GlobalTheory.TwistCheck (ev_bilL cc_log bilL_mixed balanced_iff)

variable {S : Type} [CommRing S] {d : ℕ}

theorem cz2 {n : ℕ} {a b : Pt S n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    CZ (![a, b] : Fin 2 → Pt S n d) := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem coeff_mixed (g : PS S 2 d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1) g =
      constantCoeff (pderiv (R := S) ((0 : Fin 2), i) (pderiv (R := S) ((1 : Fin 2), l) g)) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, coeff_pderiv, zero_add]
  simp

variable [Algebra ℚ S]

theorem ev_zero_log {n : ℕ} (G : FGLaw S d) (i : Fin d) : ev (n := n) ![0] (logOf G i) = 0 := by
  have e : (![0] : Fin 1 → Pt S n d) = fun _ _ => 0 := by
    funext j c; fin_cases j; rfl
  rw [e, ev_zeroFam, cc_log, map_zero]

theorem cz0 {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt S n d) i) = 0 := by simp

theorem bilinearLogForm_eval_zero_left_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![0, pt S d 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 cz0 (FBMap.cz_pt _))]
  simp [ev_zero_log]

theorem bilinearLogForm_eval_zero_right_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![pt S d 0, 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) cz0)]
  simp [ev_zero_log]

theorem bilL_add_left (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) + ev (n := 3) ![pt S d 1, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (FBMap.cz_pt _)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2c.formal_log_add_first_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_add_right (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![pt S d 0, G.add (pt S d 1) (pt S d 2)] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 1] (bilL G c) + ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (CIndFrFix2b.constantCoeff_add_second_third G)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2b.formal_log_add_last_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_swap (G : FGLaw S d) (c : Fin d → Fin d → S) (hs : ∀ i l, c i l = c l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (bilL G c) = bilL G c := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, bilL, lg, smul_eq_C_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hs l i, mul_comm (ev _ _)]

theorem canon_sub_bilin : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ β : Matrix (Fin d) (Fin d) k, βᵀ = β → (∀ a : O, (dAct k B a)ᵀ * β = β * dAct k B (star a)) → ∃ h' : PS k 2 d, B.IsCanonGauge k h' ∧ bilinPart k h' = bilinPart k h - β := by
  intro R _ d O _ _ k _ _ _ B h hc β hs hb
  let G : FGLaw k d := FBMap.mapG (algebraMap R k) B.G
  let A : OAct O G := FBMap.mapA (algebraMap R k) B.A
  have hF : B.FK k = G.F := rfl
  have hA : ∀ a, B.actK k a = A.act a := fun _ => rfl
  have p {n : ℕ} (j : Fin n) := FBMap.cz_pt (R := k) (d := d) j
  have q (a : O) (j : Fin 2) := FBMap.cz_comp1 (A.act a) (A.const a) (pt k d j) (p j)
  refine ⟨h - bilL G β, ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩, ?_⟩
  · rw [ev_sub (cz2 cz0 (p _)), hc.ax0, bilinearLogForm_eval_zero_left_eq_zero G β, sub_zero]
  · rw [ev_sub (cz2 (p _) cz0), hc.ax1, bilinearLogForm_eval_zero_right_eq_zero G β, sub_zero]
  · rw [hc.ph1, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (p _)), bilL_add_left G β]
    congr 1; ring
  · rw [hc.ph2, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (p _) (CIndFrFix2b.constantCoeff_add_second_third G)), bilL_add_right G β]
    congr 1; ring
  · rw [hc.sy, ev_sub (cz2 (p _) (p _)), bilL_swap G β (fun i l => congrFun (congrFun hs l) i)]
    congr 1; ring
  · have hbal := (balanced_iff G A a (star a) β).1 (hb a)
    rw [hc.ad a, hA, hA, ev_sub (cz2 (q _ _) (p _)), ev_sub (cz2 (p _) (q _ _)), hbal]
    congr 1; ring
  · funext i l
    have := coeff_mixed (bilL G β) i l
    rw [bilL_mixed G β] at this
    simp only [bilinPart, map_sub, this, Matrix.sub_apply]

end GlobalTheory.GaugeShift
end
end

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.HeightOneInt

theorem mulN_eq_nMul {R : Type} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    JetMomFound.mulN F n = nMul F n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [JetMomFound.mulN, nMul_succ, ih]

theorem mem_int_iff {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem isIsoGm_of_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (F : FormalGroup R) (f : PowerSeries R)
    (h0 : PowerSeries.constantCoeff f = 0) (h1 : IsUnit (PowerSeries.coeff 1 f))
    (h : (f.map φ).subst (F.map φ).toPowerSeries =
      (f.map φ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) +
        (f.map φ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) +
        (f.map φ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) *
          (f.map φ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S)) :
    JetMomFound.IsIsoGm F f := by
  refine ⟨h0, h1, ?_⟩
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hc : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f h0
  have hs : MvPowerSeries.HasSubst
      ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by
      intro s; fin_cases s <;> simp [hc])
  rw [FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin 2) φ) := by
    intro a b hab
    ext ν
    apply hφ
    rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, hab]
  apply hinj
  rw [map_add (f := _), map_add (f := _), map_mul, PowerSeries.map_subst hF, PowerSeries.map_subst (hX 0),
    PowerSeries.map_subst (hX 1), MvPowerSeries.map_X, MvPowerSeries.map_X]
  exact h

theorem htOneIsGm : JetMomFound.HtOneIsGm := by
  intro p _ F _ hH
  let φ : 𝓞_ℂ_[p] →+* ℂ_[p] := (𝓞_ℂ_[p]).subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have hI : Intg (F.map φ).toPowerSeries := by
    intro ν
    rw [FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]
    exact (mem_int_iff _).1 (MvPowerSeries.coeff ν F.toPowerSeries).2
  have hn : ∀ k, PowerSeries.coeff k (nMul (F.map φ) p) =
      ((PowerSeries.coeff k (JetMomFound.mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    intro k
    rw [← (nMul_props _ F).2.2.2.2 _ φ p, PowerSeries.coeff_map, mulN_eq_nMul]
    rfl
  obtain ⟨f, hfI, hf0, hf1, hf⟩ := HeightOne.exists_iso_multiplicative ℂ_[p] p (F.map φ) hI
    (by rw [hn]; exact hH.1) (fun k hk => by rw [hn]; exact hH.2 k hk)
  let f₀ : PowerSeries 𝓞_ℂ_[p] := PowerSeries.mk fun n =>
    ⟨PowerSeries.coeff n f, (mem_int_iff _).2 (hfI (Finsupp.single () n))⟩
  have hc : ∀ n, φ (PowerSeries.coeff n f₀) = PowerSeries.coeff n f := by
    intro n
    simp only [f₀, PowerSeries.coeff_mk]
    rfl
  have hm : f₀.map φ = f := by
    ext n
    rw [PowerSeries.coeff_map, hc]
  refine ⟨f₀, isIsoGm_of_map φ hφ F f₀ ?_ ?_ (by rw [hm]; exact hf)⟩
  · apply hφ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, map_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
  · have hne : PowerSeries.coeff 1 f ≠ 0 := by
      intro h
      rw [h, norm_zero] at hf1
      exact zero_ne_one hf1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff 1 f)⁻¹, (mem_int_iff _).2 ?_⟩ ?_
    · rw [norm_inv, hf1, inv_one]
    · apply hφ
      rw [map_mul, hc, map_one]
      exact mul_inv_cancel₀ hne

end GlobalTheory.ConvSer.HeightOneInt
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieRankSum

theorem sum_lieMult {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {g : ℕ} (hG : SmoothOfRelativeDimension g G.hom) (act : OAct (𝓞 E) G) {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (t : Sp k ⟶ S) (rk : (𝓞 E →+* k) → ℕ) (h : ∀ σ, LieMult act t σ (rk σ)) :
    ∑ σ : E →+* k, rk (σ.comp (algebraMap (𝓞 E) E)) = g := by
  classical
  have hk := isGrpPullback_pullback G t
  have hd : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hk.1 hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hd
  let actk := OAct.pullback t G act
  have hak : ∀ a, (actk.act a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv actk
  have hinj : Function.Injective fun σ : E →+* k => σ.comp (algebraMap (𝓞 E) E) := fun σ σ' e =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => RingHom.congr_fun e x
  have hσ : EigenSplit.IsSplitting fun σ : E →+* k => (RingHom.id k).comp (σ.comp (algebraMap (𝓞 E) E)) :=
    EigenSplit.isSplitting_of_isDomain hinj (NumberField.Embeddings.card E k) _
      (EigenSplit.isUnit_discr_of_charZero k)
  have hint := EigenSplit.isInternal_eigenSub hσ ρ
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint).finrank_eq
  rw [Module.finrank_directSum, Module.finrank_fin_fun] at e
  rw [← e]
  exact Finset.sum_congr rfl fun σ _ => (LieEigen.finrank_of_lieMult hk hv hak hρ (h _)).symm

theorem rank_mul_finrank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (act : OAct (𝓞 E) G) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : Sp k ⟶ S) (rk : (𝓞 E →+* k) → ℕ) (r : ℕ), (∀ σ : 𝓞 E →+* k, LieMult act t σ (rk σ) ∧ rk σ + rk (σ.comp (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) = r) → r * Module.finrank ℚ E = 2 * g := by
  intro E _ _ _ S G _ _ g hG act k _ _ _ t rk r h
  have h₁ := sum_lieMult hG act t rk fun σ => (h σ).1
  let c : (E →+* k) ≃ (E →+* k) :=
    ⟨fun σ => σ.comp (IsCMField.complexConj E : E →+* E), fun σ => σ.comp (IsCMField.complexConj E : E →+* E),
      fun σ => RingHom.ext fun a => by simp, fun σ => RingHom.ext fun a => by simp⟩
  have h₂ := (Equiv.sum_comp c fun σ => rk (σ.comp (algebraMap (𝓞 E) E))).trans h₁
  have h₃ : ∑ σ : E →+* k, (rk (σ.comp (algebraMap (𝓞 E) E)) + rk ((c σ).comp (algebraMap (𝓞 E) E))) =
      ∑ _σ : E →+* k, r := Finset.sum_congr rfl fun σ _ => (h _).2
  rw [Finset.sum_add_distrib, h₁, h₂, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    smul_eq_mul] at h₃
  rw [mul_comm, ← h₃, two_mul]

end GlobalTheory.LieRankSum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem exists_lift_ringOfIntegers {E : Type} [Field E] [NumberField E] {V K : Type} [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field K] [Algebra V K] [IsFractionRing V K] (φ : 𝓞 E →+* K) :
    ∃ ψ : 𝓞 E →+* V, ∀ a, algebraMap V K (ψ a) = φ a := by
  have hint : ∀ a, ∃ x : V, algebraMap V K x = φ a := by
    intro a
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral ℤ (φ a) := map_isIntegral_int φ h1
    exact IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top
  choose f hf using hint
  have hinj := IsFractionRing.injective V K
  refine ⟨{ toFun := f
            map_one' := hinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := hinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, hf⟩

theorem exists_dual_of_extends {V : Type} [CommRing V] {d r : ℕ} (u : Fin r → Fin d → V)
    (w : Fin d → Fin d → V) (emb : Fin r ↪ Fin d) (hw : ∀ i, w (emb i) = u i)
    (hb : ∀ x : Fin d → V, ∃! a : Fin d → V, ∀ j, ∑ k, a k * w k j = x j) :
    ∃ lam : Fin r → Fin d → V, ∀ i i', ∑ s, lam i s * u i' s = if i = i' then 1 else 0 := by
  have hsurj : Function.Surjective (Matrix.of w).vecMul := by
    intro x
    obtain ⟨a, ha, -⟩ := hb x
    exact ⟨a, funext fun j => by simpa [Matrix.vecMul, dotProduct] using ha j⟩
  have hU : IsUnit (Matrix.of w) := Matrix.vecMul_surjective_iff_isUnit.1 hsurj
  obtain ⟨N, hN⟩ := hU.exists_right_inv
  refine ⟨fun i s => N s (emb i), fun i i' => ?_⟩
  have h := congrFun (congrFun hN (emb i')) (emb i)
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [Matrix.of_apply, hw, EmbeddingLike.apply_eq_iff_eq] at h
  simp only [mul_comm (N _ _), h, eq_comm]

theorem isUnit_Ov_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : TWO.Ov v) :
    IsUnit x ↔ ¬ 0 < v (x : F) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [TWO.v_unit]
    exact lt_irrefl _
  · intro h
    have hx : (x : F) ≠ 0 := by
      intro h0
      apply h
      rw [h0, AddValuation.map_zero]
      exact WithTop.coe_lt_top (0 : ℚ)
    have hi : (x : F)⁻¹ ∈ TWO.Ov v := by
      refine TWO.exists_weight_basis_filtration (a := v (x : F)) ?_ (not_lt.1 h)
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : TWO.Ov v) (Subtype.ext (mul_inv_cancel₀ hx))

theorem exists_integral_types_and_directions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C ϖ hϖ g hg hgu hcard hnd F _ _ _ _ _ v hv
  letI := io.toAlgebra
  classical
  have hfrob := GlobalTheory.pow_sub_self_mem_span_of_splits_completely E g hg hcard hnd
  have hinj := IsFractionRing.injective T.V T.Fr
  choose σV hσV using fun τ : E →+* ℂ => exists_lift_ringOfIntegers (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have huv : ∀ ℓ i, C.ch.uvec ℓ i = algebraMap T.V T.Fr (C.uvecT ℓ i) := C.gen.1.2.2.2.2.2.2
  have hact : ∀ a j, C.ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (C.actT a j) := C.gen.1.2.1
  have hσinj : Function.Injective σV := by
    intro τ τ' h
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    have h1 : embK c τ a = embK c τ' a := io.injective (by rw [← hσV', ← hσV', h])
    have h2 := congrArg (fun z : c.F => (z : ℂ)) h1
    exact h2
  let ρ : 𝓞 E → Matrix (Fin (chD C.ch)) (Fin (chD C.ch)) T.V := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (C.actT a i)
  have hρK : ∀ a i j, dAct T.Fr C.ch.B a i j = algebraMap T.V T.Fr (ρ a i j) := by
    intro a i j
    simp only [dAct, FB.actK, hact, MvPowerSeries.coeff_map, ρ]
    rfl
  have hρF : ∀ a i j, dAct F C.ch.B a i j = algebraMap T.V F (ρ a i j) := by
    intro a i j
    simp only [dAct, FB.actK, hact, MvPowerSeries.coeff_map, ρ]
    exact (IsScalarTower.algebraMap_apply T.V T.Fr F _).symm
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (ρ a).mulVec (C.uvecT ℓ) = σV ℓ.1 a • C.uvecT ℓ := by
    intro a ℓ
    funext i
    apply hinj
    have h := congrFun (GlobalTheory.T.integral_chart_directions_are_eigenvectors E H Dw l Xo c T io y C a ℓ) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hρK, huv, ← hσV'] at h

    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    exact h
  obtain ⟨lam, hlam⟩ := GlobalTheory.exists_dual_forms_of_separated_types T.V (𝓞 E) (chD C.ch) ρ (E →+* ℂ) Dw.mult
    (fun τ a => σV τ a) C.uvecT
    (fun τ τ' hne => GlobalTheory.exists_isUnit_sub_of_ringHom_ne (𝓞 E) T.V g hg hgu hfrob _ _ (fun h => hne (hσinj h)))
    heig (fun τ => by
      obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C τ
      exact exists_dual_of_extends (fun i => C.uvecT ⟨τ, i⟩) w emb hw hb)
  choose ε hε using fun τ => GlobalTheory.exists_separating_mod_prime_pow (𝓞 E) T.V g hg hgu hfrob (E →+* ℂ) σV hσinj 1 τ
  let f : T.V →+* TWO.Ov v := TWO.fO v hϖ hv
  have hf : ∀ x, (f x : F) = algebraMap T.V F x := fun x => (IsScalarTower.algebraMap_apply T.V T.Fr F x).symm
  have hgO : ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
    intro h
    rw [← map_natCast f] at h
    exact hgu ((isUnit_map_iff f _).1 h)
  refine ⟨fun τ => f.comp (σV τ), fun ℓ i => f (C.uvecT ℓ i), fun τ a => ?_, fun ℓ i => hf _, fun ℓ i => ?_,
    fun a ℓ => ?_, fun τ a => ⟨fun h => ?_, fun h => (isUnit_Ov_iff v _).2 h⟩, fun τ a => ?_,
    ⟨fun ℓ s => f (lam ℓ s), fun ℓ ℓ' => ?_⟩, ⟨ε, fun τ τ' => ?_⟩, hgO⟩
  · rw [RingHom.comp_apply, hf, ← hσV', ← IsScalarTower.algebraMap_apply]
  · rw [hf, huv, ← IsScalarTower.algebraMap_apply]
  · funext i
    have h := congrArg (algebraMap T.V F) (congrFun (heig a ℓ) i)

    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hρF, hf, RingHom.comp_apply]
    exact h
  · exact (GlobalTheory.hom_value_congruent_int_mod_prime (𝓞 E) (TWO.Ov v) g hg hgO hfrob _ a).2
      (fun hu => (isUnit_Ov_iff v _).1 hu h)
  · have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    have h2 : σV (ComplexEmbedding.conjugate τ) a = σV τ (H.bar a) := hinj (by rw [hσV', hσV', h])
    exact congrArg f h2
  · have h := congrArg f (hlam ℓ ℓ')

    simp only [map_sum, map_mul] at h
    rw [h]
    by_cases hl : ℓ = ℓ'
    · rw [if_pos hl, if_pos hl, map_one]
    · rw [if_neg hl, if_neg hl, map_zero]
  · obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hε τ τ')
    refine Ideal.mem_span_singleton'.2 ⟨f b, ?_⟩
    have h := congrArg f hb
    rw [pow_one, map_mul, map_natCast, map_sub] at h
    rw [h, RingHom.comp_apply]
    by_cases ht : τ = τ'
    · rw [if_pos ht, if_pos ht.symm, map_one]
    · rw [if_neg ht, if_neg (Ne.symm ht), map_zero]

end GlobalTheory.PowGerm
end
