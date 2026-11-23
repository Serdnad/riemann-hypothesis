module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open Filter
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefCuspGrowth

theorem ofReal_le_growth (D : ℕ) (h : ℕ → ℕ) (r : ℕ → ℕ∞) {c : ℝ} (hc : 0 ≤ c)
    (ht : Tendsto (fun m : ℕ => (h m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial)))
    (hle : ∀ m, (h m : ℕ∞) ≤ r (m + 1)) : ENNReal.ofReal c ≤ CompHt.growth D r := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (nhds 1) := tendsto_natCast_div_add_atTop 1
  have h2 : Tendsto (fun m : ℕ => (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D))
      atTop (nhds c) := by
    have := (ht.mul (h1.pow D)).const_mul (D.factorial : ℝ)
    rwa [one_pow, mul_one, mul_div_cancel₀ _ hf.ne'] at this
  have h3 := (ENNReal.tendsto_ofReal h2).limsup_eq
  rw [CompHt.growth, ← Filter.limsup_nat_add _ 1, ← h3]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have e : (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D) =
      (D.factorial : ℝ) * (h m : ℝ) / ((m + 1 : ℕ) : ℝ) ^ D := by
    push_cast
    rw [div_pow]
    field_simp
  rw [e, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (mul_le_mul_right (by exact_mod_cast ENat.toENNReal_le.2 (hle m)) _) _

section Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem cls_L₀_nsmul (u : AllWt.Weight Dw) (k : ℕ) :
    cls (L₀ X Z (k • u)) (isLB_L₀ X Z (k • u)) = k • cls (L₀ X Z u) (isLB_L₀ X Z u) := by
  induction k with
  | zero =>
    have e := cls_common_add (common₀ X Z) (0 : AllWt.Weight Dw) 0
    simp only [add_zero] at e
    rw [zero_smul]
    exact (left_eq_add.1 e).symm ▸ rfl
  | succ k ih =>
    have e := cls_common_add (common₀ X Z) (k • u) u
    rw [succ_nsmul, succ_nsmul, ← ih]
    exact e

end Comp

section Inj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem mul_mem_vanBd (u : AllWt.Weight Dw) (k : ℕ) (h : u + k • u = (k + 1) • u)
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (g : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) :
    ((common₀ X Z).addChart h).mul θ g ∈ vanBd X Z ((k + 1) • u) := by
  intro y hy i hi
  obtain ⟨t, ha, hb, hc⟩ := ((common₀ X Z).addChart h).cover y
  rw [H0.germ_change i (((common₀ X Z).addChart h).c t) y (memTop y) hi hc,
    ((common₀ X Z).addChart h).germ_mul θ g t y (memTop y) ha hb hc]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hθ y hy _ ha))

theorem finrank_le_rank [IsIntegral (Y₀ X Z)] (u : AllWt.Weight Dw) (k : ℕ) (hC : CuspIso X Z U ((k + 1) • u))
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (hθ0 : θ ≠ 0) :
    (Module.finrank c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) : ℕ∞) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((k + 1) • wtOf Dw u 0))) := by
  have h : u + k • u = (k + 1) • u := by rw [succ_nsmul, add_comm]
  let C := (common₀ X Z).addChart h
  let φ : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤ →ₗ[c.F] Cusp Z U ((k + 1) • u) :=
    ofSpace X Z U ((k + 1) • u) ∘ₗ Submodule.inclusion hC.2 ∘ₗ
      LinearMap.codRestrict _ (C.mul θ) (mul_mem_vanBd X Z u k h hθ)
  have hφ : Function.Injective φ := by
    refine (ofSpace_injective X Z U _).comp ((Submodule.inclusion_injective hC.2).comp fun g g' e => ?_)
    have e' : C.mul θ g = C.mul θ g' := congrArg Subtype.val e
    by_contra hne
    refine GlobalTheory.Vanishing.ProdNe.mul_ne_zero C θ (g - g') hθ0 (sub_ne_zero.2 hne) ?_
    rw [map_sub, e', sub_self]
  have e : cuspOn U Z ((k + 1) • wtOf Dw u 0) = Cusp Z U ((k + 1) • u) := by
    rw [CompHt.nsmul_wtOf, smul_zero]
  rw [e]
  have hr := LinearMap.rank_le_of_injective φ hφ
  by_cases hfin : FiniteDimensional c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤)
  · rw [← Module.finrank_eq_rank] at hr
    exact (Cardinal.toENat_nat _).symm.le.trans (OrderHomClass.mono Cardinal.toENat hr)
  · rw [Module.finrank_of_not_finite hfin]
    exact bot_le

end Inj

theorem topSelf_le_growthOn : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) →
    letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) →
    ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  intro hN E _ _ _ H Dw l Xo c Y X Z r U u hV hD hC hf
  obtain ⟨f, hf⟩ := hf
  letI := algebraΓOfHom (str₀ X Z)
  intro hnef
  let S : LinSys c.F := ⟨Y₀ X Z, str₀ X Z, dimFlag Dw, L₀ X Z u, isLB_L₀ X Z u, 0, Fin.elim0⟩
  have hS : S.IsVariety := ⟨hV.1, hV.2.1, hV.2.2, hD⟩
  haveI : IsIntegral (Y₀ X Z) := hS.isIntegral
  have hp : IsProjOver (strHom c.F (X := (Y₀ X Z))) := by
    rw [strHom_eq (f := str₀ X Z) fun _ => rfl]
    exact hV.2.1
  have hdim : topologicalKrullDim (Y₀ X Z) = dimFlag Dw := ImageDegree.topologicalKrullDim_eq S hS
  have ht := hN.2.2.tendsto hp hdim hnef
  have h0 := hN.2.2.topSelf_nonneg hp hdim hnef
  let θ := ((hC u).1.equiv f).1
  have hθ : θ ∈ vanBd X Z u := (hC u).1.space_le ((hC u).1.equiv f).2
  have hθ0 : θ ≠ 0 := fun e => hf ((hC u).1.equiv.map_eq_zero_iff.1 (Subtype.ext e))
  rw [CompHt.growthOn, dimFlag_eq]
  refine ofReal_le_growth (dimFlag Dw) (fun m => lbH0 c.F (lbPow (L₀ X Z u) m)) _ (Int.cast_nonneg h0) ht fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (isLB_L₀ X Z u) m) (isLB_L₀ X Z (m • u))
    (by rw [cls_lbPow (isLB_L₀ X Z u), cls_L₀_nsmul]), ← H0.finrank_top]
  exact finrank_le_rank X Z U u m (hC _) hθ hθ0

end GlobalTheory.NefCuspGrowth
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem homotopy_identity : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (ε : Q.P →+* B) (hε : SemiHom (RingHom.id R) ε), IsDPMorphism η δ ε → (∀ b, ε (algebraMap B Q.P b) = b) → (∀ n, ε (Q.e (n + 1)) = 0) → ∀ (N : ℕ) (x : DR R Q.P), x - h.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
  intro R B _ _ _ J δ Q _ _ η v g hstd hvb hve hvd ε hε hεd hεb hεe N

  have hfilE : ∀ k, Q.e k ∈ fil η k := fun k ↦ by
    have := (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k (Q.e 1) (Q.e_one_mem_ext J)
    rwa [hstd.var] at this
  obtain ⟨hot_add, hot_alg, -, hot_rel, hot_fil⟩ := GlobalTheory.T.derivationHomotopyOperator_filtration_properties R Q.P (Q.ext J) η v Q.e N hvd hfilE
  obtain ⟨hrel_mul, -, -, -, hfil0, hfil_anti, hfil_smul⟩ := GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R Q.P (Q.ext J) η
  have hd_fil : ∀ n, ∀ x ∈ filDR R η (n + 1), dDR R Q.P x ∈ filDR R η n := fun n ↦
    (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules.2 R Q.P (Q.ext J) η v hvd n).2.1
  have hrel_le : rel R η ≤ filDR R η N := le_sup_right
  let H : DR R Q.P →+ DR R Q.P := AddMonoidHom.mk' (hot v Q.e N) hot_add
  have hH : ∀ x, H x = hot v Q.e N x := fun _ ↦ rfl
  have hrelgen : ∀ m, ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1)) ∈ rel R η := fun m ↦ by
    have : ι1 (D R Q.P (η.dpow (m + 1) (Q.e 1)) - η.dpow m (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
      Ideal.subset_span ⟨m, Q.e 1, Q.e_one_mem_ext J, rfl⟩
    rwa [hstd.var, hstd.var, map_sub, map_smul] at this
  have hD0 : ι1 (D R Q.P (Q.e 0)) = 0 := by rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]
  have hε1 : ε (Q.e 1) = 0 := by simpa using hεe 0
  have hcomp : ∀ α : DR R B, hε.mDR (g.mDR α) = α := by
    intro α
    induction α using indDR with
    | h b => rw [g.mDR_algebraMap, hε.mDR_algebraMap, hεb]
    | hd b => rw [g.mDR_ι, hε.mDR_ι, g.m1_D, hε.m1_D, hεb]
    | hm x y hx hy => rw [map_mul, map_mul, hx, hy]
    | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hεD1 : hε.mDR (ι1 (D R Q.P (Q.e 1))) = 0 := by
    rw [hε.mDR_ι, hε.m1_D, hε1, Derivation.map_zero, map_zero]

  have big : ∀ M, ∀ x ∈ filDR R η M, N ≤ M →
      x - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
    intro M x hx hM
    refine sub_mem (sub_mem (hfil_anti N M hM hx) ?_) ?_
    · exact hfil_anti N M hM (hd_fil M _ (hot_fil M x hx))
    · cases M with
      | zero => rw [Nat.le_zero.1 hM, hfil0]; trivial
      | succ k => exact hfil_anti N (k + 1) hM (hot_fil k _ (hd_fil k x hx))
  have hsmul_mem : ∀ n (y : DR R Q.P), Q.e n • y ∈ filDR R η n := fun n y ↦ by
    simpa using hfil_smul n 0 (Q.e n) (hfilE n) y (by rw [hfil0]; trivial)
  intro x
  refine GlobalTheory.T.pdPolynomial_compatibleForms_generated_induction R B J δ Q η v g hstd hvb hve hvd
    (fun x ↦ x - g.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N)
    ?_ ?_ ?_ ?_ x
  ·
    intro x hx
    refine sub_mem (sub_mem (sub_mem (hrel_le hx) (hrel_le ?_)) (hrel_le ?_)) (hrel_le ?_)
    · exact mDR_mem_rel g hstd.dp (mDR_mem_rel hε hεd hx)
    · exact dDR_mem_rel R η (hot_rel x hx)
    · exact hot_rel _ (dDR_mem_rel R η hx)
  ·
    intro x y hx hy
    have := add_mem hx hy
    convert this using 1
    simp only [map_add (f := _), hot_add]
    abel
  ·
    intro n α
    have hz := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n α).1
    have hz' := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).1
    have hdx : dDR R Q.P (Q.e n • g.mDR α) = ι1 (D R Q.P (Q.e n)) * g.mDR α + Q.e n • g.mDR (dDR R B α) := by
      rw [dDR_smul, g.mDR_dDR]
    have hmx : g.mDR (hε.mDR (Q.e n • g.mDR α)) = algebraMap B Q.P (ε (Q.e n)) • g.mDR α := by
      rw [hε.mDR_smul, hcomp, g.mDR_smul]
    rw [hmx, hz, hdx, hot_add, hz', map_zero]
    cases n with
    | zero =>
      rw [hD0, zero_mul, Q.e_zero, map_one, map_one, one_smul, ← hH, map_zero]
      simp
    | succ m =>
      rw [hεe m, map_zero, zero_smul]
      rcases lt_or_ge m N with hm | hm
      · have hv := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N m α).2 hm
        have hr : (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η :=
          hrel_mul _ (hrelgen m) _
        have key : ι1 (D R Q.P (Q.e (m + 1))) * g.mDR α =
            (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
              Q.e m • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) := by
          rw [sub_mul, smul_mul_assoc]; abel
        rw [key, hot_add, hv]
        have : Q.e (m + 1) • g.mDR α - 0 - 0 -
            (hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) +
              Q.e (m + 1) • g.mDR α + 0) =
            -hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) := by abel
        rw [this]
        exact hrel_le (neg_mem (hot_rel _ hr))
      · have hb := big (m + 1) _ (hsmul_mem (m + 1) (g.mDR α)) (by omega)
        rw [hz, hdx, hot_add, hz', map_zero] at hb
        simpa using hb
  ·
    intro n α
    have hdy : dDR R Q.P (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = -(ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α)) := by
      rw [dDR_mul, sgn_ι, dDR_D, zero_mul, add_zero, neg_mul, g.mDR_dDR]
    have hmx : g.mDR (hε.mDR (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α))) = 0 := by
      rw [hε.mDR_smul, map_mul, hεD1, zero_mul, smul_zero, map_zero]
    rw [hmx, sub_zero]
    rcases lt_or_ge n N with hn | hn
    · have hv := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n α).2 hn
      have hv' := (GlobalTheory.T.dividedPowerHomotopyOperator_values_generators R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).2 hn

      have hr2 : ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) ∈ rel R η := by
        cases n with
        | zero => rw [hD0, zero_mul]; exact zero_mem _
        | succ k =>
          have : ι1 (D R Q.P (Q.e (k + 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) =
              (ι1 (D R Q.P (Q.e (k + 1))) - Q.e k • ι1 (D R Q.P (Q.e 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) := by
            have hsq : Q.e k • ι1 (D R Q.P (Q.e 1)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = 0 := by
              rw [smul_mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero]
            rw [sub_mul, hsq, sub_zero]
          rw [this]
          exact hrel_mul _ (hrelgen k) _
      have hr1 : (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η :=
        hrel_mul _ (hrelgen n) _
      have hdx : dDR R Q.P (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) =
          ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) -
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α)) := by
        rw [dDR_smul, hdy, smul_neg, sub_eq_add_neg]
      have hdh : dDR R Q.P (Q.e (n + 1) • g.mDR α) =
          (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α) := by
        rw [dDR_smul, g.mDR_dDR, sub_mul, smul_mul_assoc]; abel
      rw [hv, hdh, hdx, ← hH, map_sub, hH, hH, hv']
      have : Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) -
          ((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α)) -
          (hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) -
            Q.e (n + 1) • g.mDR (dDR R B α)) =
          -((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α) -
            hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) := by abel
      rw [this]
      exact hrel_le (sub_mem (neg_mem hr1) (hot_rel _ hr2))
    · exact big n _ (hsmul_mem n _) hn

end GlobalTheory.PDForm
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.ConnCocycle

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem divPowerCompatDeRhamRelIdeal_zero_dividedPowers (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : rel R (dp0 B) = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨n, a, ha, rfl⟩
  rw [Ideal.mem_bot.1 ha]
  simp [dpow_eval_zero]

theorem cocyc {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (k : (KK (dp0 R) s).Z1)
    {T T' : Thick (dp0 R) s} (φ : T ⟶ T') :
    k.1.2 T' = km1 (SemiHom.of_algHom φ.φ) φ.dp (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ) := by
  have h := congrArg (fun c ↦ c.2.1 T T' φ) (AddMonoidHom.mem_ker.1 k.2)
  change k.1.2 T' - _ - _ = 0 at h
  rw [sub_sub, sub_eq_zero] at h
  exact h

section
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def sndK : (diagExt R B).C →+ K1 R (dp0 B) :=
  AddMonoidHom.mk' (fun c ↦ Submodule.Quotient.mk (TrivSqZeroExt.snd c)) fun a b ↦ by
    rw [TrivSqZeroExt.snd_add, Submodule.Quotient.mk_add]

theorem sndK_apply (c : (diagExt R B).C) : sndK R B c = Submodule.Quotient.mk (TrivSqZeroExt.snd c) := rfl

theorem sndK_mul (x y : (diagExt R B).C) :
    sndK R B (x * y) = (diagExt R B).π x • sndK R B y + (diagExt R B).π y • sndK R B x := by
  show Submodule.Quotient.mk (x * y).snd = x.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) y.snd +
    y.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) x.snd
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1

theorem sndK_alg (r : R) : sndK R B (algebraMap R (diagExt R B).C r) = 0 := by
  rw [sndK_apply, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, Submodule.Quotient.mk_zero]

theorem sndK_dpow (n : ℕ) (a : (diagExt R B).C) (ha : a ∈ RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) :
    sndK R B ((divided₂ (diagExt R B).sq).dpow (n + 1) a) =
      (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow n a) • sndK R B a := by
  rcases n with _ | m
  · rw [(divided₂ (diagExt R B).sq).dpow_one ha, (divided₂ (diagExt R B).sq).dpow_zero ha, map_one, one_smul]
  · have h0 : (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow (m + 1) a) = 0 :=
      (divided₂ (diagExt R B).sq).dpow_mem (Nat.succ_ne_zero m) ha
    rw [squareZeroDividedPowers_dpow _ (by omega), map_zero, h0, zero_smul]

end

section
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem deRhamAlgebraMap_sends_sectionOneForm (ρ : DR R (diagExt R B).C →+ DR R B) (hmul : ∀ x y, ρ (x * y) = ρ x * ρ y)
    (halg : ∀ c, ρ (algebraMap _ (DR R (diagExt R B).C) c) = algebraMap B (DR R B) ((diagExt R B).π c))
    (hD : ∀ c, ρ (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c))
    (α : B →ₐ[R] (diagExt R B).C) (hα : ∀ b, (diagExt R B).π (α b) = b)
    (g : Ω[B⁄R] →+ Ω[B⁄R]) (hg : ∀ b c : B, g (b • D R B c) = b • TrivSqZeroExt.snd (α c))
    (κ : Ω[B⁄R]) : ρ (ι1 ((SemiHom.of_algHom α).m1 κ)) = ι1 (g κ) := by
  induction κ using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, Algebra.smul_def, hmul, halg, hD, hg, map_smul,
      Algebra.smul_def]
    congr 2
    exact hα b
  | h0 => simp
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

end

theorem form_eq_connForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (k : (KK (dp0 R) s).Z1)
    (f : Z1 (O (dp0 R) s)), k.1.1 = f.1 → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)),
    k.1.2 (Thick.triv B x hx) = Submodule.Quotient.mk (connForm f x hx) := by
  intro R _ X s k f hk B _ _ x hx
  obtain ⟨ρ, hadd, hmul, halg, hD, hrel, -, -⟩ := GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R B ⊥ (dp0 B) (diagExt R B).C
    (RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) (divided₂ (diagExt R B).sq) (diagExt R B).π
    (sndK R B) (sndK_mul R B) (sndK_alg R B) (sndK_dpow R B)
  have h0 := divPowerCompatDeRhamRelIdeal_zero_dividedPowers R B
  simp only [h0, Ideal.mem_bot, sub_sub, sub_eq_zero] at hadd hmul halg hD hrel
  let ρh : DR R (diagExt R B).C →+ DR R B := AddMonoidHom.mk' ρ hadd
  have hD' : ∀ c, ρh (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c) := fun c ↦ hD c _ rfl
  let a := (diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl
  let a' := (diagExt R B).secHom hx (diagSec R B) (fst_derSec _)
  have c1 := cocyc k a
  have c2 := cocyc k a'
  rw [hk] at c1 c2
  obtain ⟨κ, hκ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 (Thick.triv B x hx))
  obtain ⟨θ, hθ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 ((diagExt R B).thick x hx))
  rw [← hκ, ← hθ, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at c1 c2
  have e1 : ρh (ι1 (θ - ((SemiHom.of_algHom a.φ).m1 κ + D R _ (f.1 _ _ a)))) = 0 := hrel _ c1
  have e2 : ρh (ι1 (θ - ((SemiHom.of_algHom a'.φ).m1 κ + D R _ (f.1 _ _ a')))) = 0 := hrel _ c2
  have r1 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a.φ (fun _ ↦ rfl) 0 (fun b c ↦ by
    show (0 : Ω[B⁄R]) = b • TrivSqZeroExt.snd (TrivSqZeroExt.inl c : TrivSqZeroExt B Ω[B⁄R])
    rw [TrivSqZeroExt.snd_inl, smul_zero])
  have r2 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a'.φ (fst_derSec _) (AddMonoidHom.id _) (fun b c ↦ by
    show b • D R B c = b • TrivSqZeroExt.snd (diagSec R B c)
    rw [snd_derSec])
  simp only [map_sub, map_add (f := _), r1, r2, hD', AddMonoidHom.zero_apply, AddMonoidHom.id_apply, map_zero,
    zero_add] at e1 e2
  rw [← hκ, Submodule.Quotient.eq]
  change ι1 _ ∈ rel R (dp0 B)
  rw [h0, Ideal.mem_bot, map_sub, sub_eq_zero]
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  change ι1 κ = ι1 (TrivSqZeroExt.snd (f.1 _ _ a)) - ι1 (TrivSqZeroExt.snd (f.1 _ _ a'))
  linear_combination (norm := abel1) e1 - e2

end GlobalTheory.ConnCocycle
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ deg q = Nat.card G ∧ (ptMap q).ker = G ∧ ∀ (C : AbVar K) (f : A ⟶ C), G ≤ (ptMap f).ker → ∃ g : B ⟶ C, q ≫ g = f := by
  first | (exact @GlobalTheory.AV.AbVar.exists_quot_of_galois_stable) | (exact GlobalTheory.AV.AbVar.exists_quot_of_galois_stable) | (intros; apply GlobalTheory.AV.AbVar.exists_quot_of_galois_stable  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.isThetaFunO_of_matchedSquare_bigRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ d ∈ Θ.support, IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  first | exact @GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched | exact GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched | (intros; apply GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched <;> assumption)
end
