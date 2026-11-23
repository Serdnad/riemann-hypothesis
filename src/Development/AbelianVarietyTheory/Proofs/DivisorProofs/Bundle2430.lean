module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
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
import Mathlib.SetTheory.ZFC.PSet
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

namespace GlobalTheory.CovTop.Sizes

theorem eventually_scale {eps : ℝ} (he : 0 < eps) (A M : ℝ) : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    M ≤ x ^ eps ∧ 10 ≤ x ^ eps ∧ 1 ≤ Real.log (Real.log x) ∧ (x ^ A) ^ M ≤ Real.exp (x ^ eps) ∧ 5 ≤ x ^ (eps / 5) ∧
      (10 : ℝ) ^ 60 ≤ x := by
  have h1 := (tendsto_rpow_atTop he).eventually_ge_atTop M
  have h2 := (tendsto_rpow_atTop he).eventually_ge_atTop 10
  have h3 := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  have h5 := (tendsto_rpow_atTop (by positivity : 0 < eps / 5)).eventually_ge_atTop 5
  have h6 := Filter.eventually_ge_atTop ((10 : ℝ) ^ 60)
  have h4 := ((isLittleO_log_rpow_atTop he).const_mul_left (A * M)).bound one_pos
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (h3.and (h4.and (h5.and h6)))))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx0 x hx
  have hx0' : 0 < x := lt_of_lt_of_le (by norm_num) a6
  refine ⟨a1, a2, a3, ?_, a5, a6⟩
  rw [← Real.rpow_mul hx0'.le, Real.rpow_def_of_pos hx0', Real.exp_le_exp]
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0' eps)] at a4
  rw [mul_comm]
  exact (le_abs_self _).trans a4

theorem coprime_fifteen {g : ℕ} (hg : g.Prime) (h : 15 < g) : Nat.Coprime 15 g :=
  ((Nat.Prime.coprime_iff_not_dvd hg).2 fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (not_le.2 h)).symm

theorem hostNum_of_sizes {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (T : ParamsT D L P) (S : SizesAt L) {A M : ℝ}
    (hg : ∀ k, Real.log (D.host.g k : ℝ) ≤ 9 * L.sc.L + 1) (hA : 22 + L.Ct ≤ A)
    (a1 : M ≤ L.sc.L) (a2 : 10 ≤ L.sc.L) (a3 : 1 ≤ Real.log (Real.log L.sc.x)) (a4 : (L.sc.x ^ A) ^ M ≤ L.sc.b)
    (a5 : 5 ≤ L.sc.x ^ (L.sc.ez / 5)) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x) : HostNum D L T.PP A M := by
  have hfr := Pm.fr_le_pow S hx
  obtain ⟨sN, -, -, -, -, -, sQD, -, -, -, -, -, -, -, -, -, -, sW, -, -, sG, -, -⟩ := S
  have hx1 := L.sc.one_lt_alt.le
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hL := Pm.one_le_L L
  have hf := Pm.two_le_f D
  have hr := Pm.six_le_r D
  have hrt := Pm.r_le_alt_alt D
  have hLx : L.sc.L ≤ L.sc.x := by
    calc L.sc.L = L.sc.x ^ L.sc.eps := rfl
      _ ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = L.sc.x := Real.rpow_one _
  have hnV : (D.R.nV : ℝ) ≤ 2 * D.R.t := by
    have : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
    linarith
  have hnV0 : (0 : ℝ) < D.R.nV := by
    have : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
    linarith
  have hCt : 0 ≤ L.Ct := by
    by_contra hc
    have := Real.rpow_lt_one_of_one_lt_of_neg L.sc.one_lt_alt (not_le.1 hc)
    linarith [L.t_win.1, L.t_win.2]
  have hgl : ∀ k, 15 < D.host.g k := fun k => by
    have hk : (1 : ℝ) ≤ D.R.k := by
      have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
      exact_mod_cast this
    have hb : (2 : ℝ) ≤ L.sc.b := by
      have := Real.add_one_le_exp L.sc.L
      unfold Scale.b
      linarith
    have h2 : (2 : ℝ) ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h3 : (2 : ℝ) ^ 8 ≤ D.host.g k := (pow_le_pow_left₀ (by norm_num) h2 8).trans (sG k k).1
    have h4 : ((15 : ℕ) : ℝ) < D.host.g k := lt_of_lt_of_le (by norm_num) h3
    exact_mod_cast h4
  refine ⟨⟨a1, a2, hLx, a3⟩, ?_, ?_, ⟨?_, ?_⟩, hg, ?_, ?_, ?_, ?_, ?_, ⟨by linarith, ?_, ?_⟩, a4, sW⟩
  · have h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) := by
      calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith)
    have h2 : (4 : ℝ) ≤ D.R.n := le_trans (by norm_num) (hx.trans (h1.trans sN.1))
    have h3 : ((8 : ℕ) : ℝ) ≤ D.R.f := by rw [Pm.f_eq]; push_cast; linarith
    exact_mod_cast h3
  · have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    rw [h1]; unfold Ranks.f Ranks.n; ring
  · rw [Real.log_mul (by linarith) (by linarith)]
    linarith [Pm.log_f_le P, Pm.log_r_le P]
  · have h1 := Real.log_le_log hnV0 hnV
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith [(Pm.log_cond_le P).2, Real.log_two_lt_d9]
  · have h : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * L.sc.L := logdE_le_two_f_L P
    nlinarith
  · exact sQD.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))
  · exact le_trans (Nat.le_floor (by exact_mod_cast a5)) L.split_tie
  · exact Nat.Coprime.mul_right (coprime_fifteen (D.host.g_prime 0) (hgl 0)) (coprime_fifteen (D.host.g_prime 1) (hgl 1))
  · have hZ := Pm.one_le_Z L
    have h1 : zBase L ^ 12 ≤ zBase L ^ T.eP := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)
    rw [T.PP_eq]
    exact h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)
  · exact T.PP_poly.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  · have h2 : (D.R.nV : ℝ) ≤ L.sc.x * L.sc.x ^ L.Ct :=
      hnV.trans (mul_le_mul (le_trans (by norm_num) hx) L.t_win.2 (by positivity) hx0.le)
    calc (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L ≤ L.sc.x ^ (20 : ℝ) * (L.sc.x * L.sc.x ^ L.Ct) * L.sc.x := by gcongr
      _ = L.sc.x ^ (20 + (1 + L.Ct) + 1) := by
        rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

theorem hostN : ∀ M : ℝ, HostN M := by
  intro M
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := eventually_scale he (22 + |Fm.Ct|) M
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 5)
  refine ⟨22 + |Fm.Ct|, by positivity, max x0 x2, fun x hx hle ι p _ _ => ?_⟩
  obtain ⟨a1, a2, a3, a4, -, a6⟩ := hx0 x ((le_max_left _ _).trans hle)
  have a5 : 5 ≤ x ^ (Fm.ez / 5) := hx2 x ((le_max_right _ _).trans hle)
  have hsz : (Fm.L x ι).sc.ez = Fm.ez := Fm.toFamCore.L_ez x ι
  have hsx : (Fm.L x ι).sc.x = x := Fm.L_x x ι hx
  have hse : (Fm.L x ι).sc.eps = eps := Fm.L_eps x ι
  have hsL : (Fm.L x ι).sc.L = x ^ eps := by unfold Scale.L; rw [hsx, hse]
  have hg : ∀ k, Real.log ((Fm.D x ι).host.g k) ≤ 9 * (Fm.L x ι).sc.L + 1 := fun k => by
    have hlo : 0 < ((((Fm.D x ι).host.g k : ℕ)) : ℝ) := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    have := (Real.log_le_iff_le_exp hlo).2 ((hF.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1 k)
    linarith
  refine hostNum_of_sizes (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) hg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Fm.Ct_eq]; linarith [le_abs_self Fm.Ct]
  · rwa [hsL]
  · rwa [hsL]
  · rwa [hsx]
  · unfold Scale.b; rwa [hsL, hsx]
  · rwa [hsx, hsz]
  · rwa [hsx]

end GlobalTheory.CovTop.Sizes

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep.LiftFn

variable {Y : Scheme.{0}}

theorem eq_of_specializes_of_coheight {v w : Y} (h : v ⤳ w) (hv : Order.coheight v = 1)
    (hw : Order.coheight w = 1) : v = w := by
  by_contra hne
  have hlt : w < v := lt_of_le_not_ge h fun e => hne (Specializes.antisymm h e).eq
  have h₃ := Order.coheight_add_one_le hlt
  rw [hv, hw] at h₃
  exact absurd h₃ (by decide)

variable [IsIntegral Y] [IsLocallyNoetherian Y]

theorem mult_neg (F : CartierDiv Y) (z : Y) : (-F).mult z = -F.mult z := by
  have e := CartierDiv.mult_add F (-F) z
  rw [add_neg_cancel, (CartierDiv.isEqn_zero (X := Y) z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero] at e
  omega

end GlobalTheory.PairStep.LiftFn

namespace GlobalTheory.PairStep


open LiftFn in
theorem exists_lifted_fn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  intro X _ _ p n hp _ η m G N Y _ _ s _ K B F hres hcoh y σ hF hσy hσ
  have hpr : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hspr : IsProper (s ≫ p) :=
    ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper s := IsProper.of_comp s p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)

  set T : Set Y := {v | v ≠ σ ∧ 0 < F.mult v} with hTdef
  have hT : T.Finite := F.finite_support_mult.subset fun v hv => hv.2.ne'
  obtain ⟨U, e, hUa, hyU, hNe, hav⟩ := GlobalTheory.T.exists_affine_nhds_avoiding_images_of_specializations X Y s T σ y N hT
    fun v hv w hvw hσw hwy => not_le.2 hv.2 (hF v w hv.1 hvw hσw hwy)
  have hTc : IsClosed (⋃ v ∈ T, closure ({v} : Set Y)) :=
    hT.isClosed_biUnion fun _ _ => isClosed_closure
  set W₁ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, hTc.isOpen_compl⟩ with hW₁
  set W₂ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, (isClosed_closure (s := ({σ} : Set Y))).isOpen_compl⟩ with hW₂
  have hW : W₁ ⊔ W₂ = s ⁻¹ᵁ U := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    by_cases hwσ : w ∈ closure ({σ} : Set Y)
    · refine Or.inl ⟨hw, fun hwT => ?_⟩
      obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 hwT
      exact hav v hv w (specializes_iff_mem_closure.2 hwv) (specializes_iff_mem_closure.2 hwσ) hw
    · exact Or.inr ⟨hw, hwσ⟩
  have hc := hcoh U hUa
  rw [← hW] at hc
  set e' : Y.functionFieldˣ := fnPull s e with he'
  have key : ∀ w ∈ s ⁻¹ᵁ U, ∀ f : Y.functionField,
      (pullCart s N - F).RegularAt w f ↔ (-F).RegularAt w (f * e') := by
    intro w hw f
    obtain ⟨g, hg⟩ := F.exists_isEqn w
    rw [((isEqn_pullCart s (hNe _ hw)).sub hg).regularAt_iff, hg.neg.regularAt_iff]
    have : f * ((fnPull s e / g : Y.functionFieldˣ) : Y.functionField) =
        f * (e' : Y.functionField) * ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      rw [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, he']
      ring
    rw [this]
  have hinv : ∀ x ∈ W₁ ⊓ W₂, (pullCart s N - F).RegularAt x (e' : Y.functionField)⁻¹ := by
    intro x hx
    rw [key x hx.1.1, inv_mul_cancel₀ e'.ne_zero]
    have h1 := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg Y (-F) x 1).2
    rw [Units.val_one] at h1
    refine h1 fun z hzx => ?_
    rw [(unitAt_one z).ord_eq_zero, zero_add, mult_neg]
    refine neg_nonneg.2 (not_lt.1 fun hz => ?_)
    by_cases hzσ : z = σ
    · subst hzσ
      exact hx.2.2 (specializes_iff_mem_closure.1 hzx)
    · exact hx.1.2 (Set.mem_iUnion₂.2 ⟨z, ⟨hzσ, hz⟩, specializes_iff_mem_closure.1 hzx⟩)
  obtain ⟨h₁, h₂, hsplit, hh₁, hh₂⟩ :=
    GlobalTheory.T.rational_function_split_regular_divisor Y (pullCart s N - F) W₁ W₂ hc (e' : Y.functionField)⁻¹ hinv
  have hσU : σ ∈ s ⁻¹ᵁ U := hσy.mem_open U.isOpen hyU
  refine ⟨h₂ * e', ?_, fun v hvσ hv hvy => ?_⟩
  · have hσW : σ ∈ W₁ := ⟨hσU, fun hσT => by
      obtain ⟨v, hv, hσv⟩ := Set.mem_iUnion₂.1 hσT
      exact hv.1 (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hσv)
        (CartierDiv.coheight_eq_one_of_mult_ne_zero hv.2.ne') hσ)⟩
    have e₁ : h₂ * (e' : Y.functionField) - 1 = h₁ * e' := by
      rw [show h₂ = (e' : Y.functionField)⁻¹ + h₁ by rw [hsplit]; ring, add_mul,
        inv_mul_cancel₀ e'.ne_zero]
      ring
    rw [e₁]
    exact (key σ hσU h₁).1 (hh₁ σ hσW)
  · have hvU : v ∈ s ⁻¹ᵁ U := hvy.mem_open U.isOpen hyU
    have hvW : v ∈ W₂ := ⟨hvU, fun hvσ' =>
      hvσ (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hvσ') hσ hv).symm⟩
    exact (key v hvU h₂).1 (hh₂ v hvW)

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_nbhd_specializes_of_isClosed {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : Set Y) (hF : IsClosed F) (hη : genericPoint Y ∉ F) {y : Y} {O : Y.Opens} (hy : y ∈ O) :
    ∃ V : Y.Opens, y ∈ V ∧ V ≤ O ∧
      ∀ y' ∈ V, ∀ v, v ⤳ y' → Order.coheight v = 1 → v ∈ F → v ⤳ y := by
  classical
  obtain ⟨W, hW, hyW, hWO⟩ := exists_isAffineOpen_mem_and_subset hy
  haveI := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hN : NoetherianSpace W := by
    have := NoetherianSpace.range hW.fromSpec hW.fromSpec.continuous
    rw [hW.range_fromSpec] at this
    exact this
  have hC : IsClosed ((Subtype.val : W → Y) ⁻¹' F) := hF.preimage continuous_subtype_val
  obtain ⟨S, hS, hc, hi, hU⟩ := @NoetherianSpace.exists_finite_set_isClosed_irreducible _ _ hN _ hC
  let y₀ : W := ⟨y, hyW⟩
  let bad : Set W := ⋃₀ {T ∈ S | y₀ ∉ T}
  have hS' : {T ∈ S | y₀ ∉ T}.Finite := hS.subset fun T hT => hT.1
  have hbad : IsClosed bad := by
    change IsClosed (⋃₀ {T ∈ S | y₀ ∉ T})
    rw [Set.sUnion_eq_biUnion]
    exact hS'.isClosed_biUnion fun T hT => hc T hT.1
  refine ⟨⟨Subtype.val '' badᶜ, W.isOpen.isOpenMap_subtype_val _ hbad.isOpen_compl⟩,
    ⟨y₀, ?_, rfl⟩, ?_, ?_⟩
  · rintro ⟨T, ⟨-, hyT⟩, hyT'⟩
    exact hyT hyT'
  · rintro _ ⟨x, -, rfl⟩
    exact hWO x.2
  · rintro _ ⟨x, hx, rfl⟩ v hv hcv hvF
    have hvW : v ∈ W := hv.mem_open W.isOpen x.2
    let v' : W := ⟨v, hvW⟩
    have hv' : v' ⤳ x := Topology.IsInducing.subtypeVal.specializes_iff.1 hv
    have hvS : v' ∈ ⋃₀ S := hU ▸ hvF
    obtain ⟨T, hT, hvT⟩ := hvS
    have hxT : x ∈ T := hv'.mem_closed (hc T hT) hvT
    have hyT : y₀ ∈ T := by
      by_contra h
      exact hx ⟨T, ⟨hT, h⟩, hxT⟩
    obtain ⟨g, hg⟩ := QuasiSober.sober (hi T hT) (hc T hT)
    have hgF : g.1 ∈ F := by
      have : g ∈ ⋃₀ S := ⟨T, hT, hg.mem⟩
      rw [← hU] at this
      exact this
    have hgv : g.1 ⤳ v := Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hvT)
    have hgy : g.1 ⤳ y := Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hyT)
    have hgη : g.1 < genericPoint Y := by
      refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
      have e' : g.1 = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
      exact hη (e' ▸ hgF)
    have hvg : v = g.1 := by
      by_contra hne
      have h₃ := Order.coheight_add_one_le (show v < g.1 from lt_of_le_not_ge hgv fun e =>
        hne (Specializes.antisymm e hgv).eq)
      have h₄ := Order.coheight_add_one_le hgη
      rw [hcv] at h₃
      have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
      exact absurd h₅ (by decide)
    rw [hvg]
    exact hgy

theorem isSncChart_spread : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ)
    (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ),
    genericPoint Y ∉ B → IsSncChart q n B y U hy z J w u → ∃ V : Y.Opens, y ∈ V ∧ ∀ y' ∈ V,
      ∃ (hy' : y' ∈ U) (J' : Finset (Fin n)), J' ⊆ J ∧ IsSncChart q n B y' U hy' z J' w u ∧
        ∀ j ∈ J', y' ∉ Y.basicOpen (z j) := by
  intro Y _ _ q n _ B y U hy z J w u hη hc
  classical
  have hηb : ∀ j ∈ J, genericPoint Y ∈ Y.basicOpen (z j) := fun j hj =>
    (Y.mem_basicOpen (z j) _ (gen_mem hy)).2 (by
      have : IsUnit (u j : Y.functionField) := (u j).isUnit
      rw [hc.val j hj] at this
      exact this)
  have hord0 : ∀ j ∈ J, ∀ v ∈ Y.basicOpen (z j), Scheme.ord (u j : Y.functionField) v = 0 := by
    intro j hj v hv
    haveI : Nonempty (Y.basicOpen (z j)) := ⟨⟨v, hv⟩⟩
    have h1 := Scheme.ord_of_isUnit (U := Y.basicOpen (z j))
      (Y.toRingedSpace.isUnit_res_basicOpen (z j)) hv
    rw [hc.val j hj, ← h1]
    congr 1
    exact (Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le (z j))) _ _ (z j)).symm
  let F : Set Y := (B : Set Y) ∪ ⋃ j ∈ J, ((Y.basicOpen (z j) : Set Y))ᶜ
  have hF : IsClosed F := B.isClosed.union
    (isClosed_biUnion_finset fun j _ => (Y.basicOpen (z j)).isOpen.isClosed_compl)
  have hηF : genericPoint Y ∉ F := by
    rintro (h | h)
    · exact hη h
    · obtain ⟨j, hj, h⟩ := Set.mem_iUnion₂.1 h
      exact h (hηb j hj)
  obtain ⟨V, hyV, hVU, hV⟩ := exists_nbhd_specializes_of_isClosed F hF hηF hy
  refine ⟨V, hyV, fun y' hy' => ?_⟩
  have hy'U : y' ∈ U := hVU hy'
  refine ⟨hy'U, J.filter (fun j => w j ⤳ y'), Finset.filter_subset _ _,
    ⟨hc.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    exact hc.val j (Finset.mem_filter.1 hj).1
  · intro j hj
    exact (Finset.mem_filter.1 hj).2
  · intro j hj
    exact hc.coheight j (Finset.mem_filter.1 hj).1
  · exact hc.inj.mono fun j hj => (Finset.mem_filter.1 hj).1
  · intro j hj
    exact hc.ord_self j (Finset.mem_filter.1 hj).1
  · intro j hj v hv hne
    have hjJ := (Finset.mem_filter.1 hj).1
    by_cases hb : v ∈ Y.basicOpen (z j)
    · exact hord0 j hjJ v hb
    by_cases hcv : Order.coheight v = 1
    · exact hc.ord_other j hjJ v (hV y' hy' v hv hcv (Or.inr (Set.mem_iUnion₂.2 ⟨j, hjJ, hb⟩))) hne
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hcv _
  · intro v hv hcv
    constructor
    · intro hvB
      obtain ⟨j, hj, rfl⟩ := (hc.mem v (hV y' hy' v hv hcv (Or.inl hvB)) hcv).1 hvB
      exact ⟨j, Finset.mem_filter.2 ⟨hj, hv⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hjJ := (Finset.mem_filter.1 hj).1
      exact (hc.mem _ (hc.spec j hjJ) hcv).2 ⟨j, hjJ, rfl⟩
  · intro j hj hb
    have hjJ := (Finset.mem_filter.1 hj).1
    have h0 := hord0 j hjJ (w j) ((Finset.mem_filter.1 hj).2.mem_open (Y.basicOpen (z j)).isOpen hb)
    rw [hc.ord_self j hjJ] at h0
    exact one_ne_zero h0

end GlobalTheory.PairStep
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp


theorem _root_.GlobalTheory.T.anchoredWeight_indefiniteLift_gaps : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
    (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m), (i : ℕ) + 1 < D.R.m →
    (dat p i).p + (dat p i).q = D.R.r ∧ GlobalTheory.FlagTan.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 ∧
    ∀ (τ : Psi p.T.Q.H) (k : ℕ), k + 1 < (dat p i).p + (dat p i).q →
      (k + 1 ≠ (dat p i).p → min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) - 2 ≤ (gap (uW p i τ) k : ℝ)) ∧
      (k + 1 = (dat p i).p → LevelStarExponents.h0 L + D.R.r - 3 ≤ (gap (uW p i τ) k : ℝ)) := by
  first | exact @GlobalTheory.RecGaps.gaps | exact GlobalTheory.RecGaps.gaps | (intros; apply GlobalTheory.RecGaps.gaps <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.compatibleFormsCocycle_form_eq_connectionForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (k : (KK (dp0 R) s).Z1) (f : Z1 (O (dp0 R) s)), k.1.1 = f.1 → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)), k.1.2 (Thick.triv B x hx) = Submodule.Quotient.mk (connForm f x hx) := by
  first | exact @GlobalTheory.ConnCocycle.form_eq_connForm | exact GlobalTheory.ConnCocycle.form_eq_connForm | (intros; apply GlobalTheory.ConnCocycle.form_eq_connForm <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.dividedPowerPolyAlgebra_homotopy_identity : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (ε : Q.P →+* B) (hε : SemiHom (RingHom.id R) ε), IsDPMorphism η δ ε → (∀ b, ε (algebraMap B Q.P b) = b) → (∀ n, ε (Q.e (n + 1)) = 0) → ∀ (N : ℕ) (x : DR R Q.P), x - h.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
  first | exact @GlobalTheory.PDForm.homotopy_identity | exact GlobalTheory.PDForm.homotopy_identity | (intros; apply GlobalTheory.PDForm.homotopy_identity <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.exists_diagonal_firstNeighbourhood_retraction_forms : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R), ∃ (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S) (r1 : ∀ T, (KK κ t).M1.obj (S.obj T) →+ (KK κ t).M1.obj T) (r2 : ∀ T, (KK κ t).M2.obj (S.obj T) →+ (KK κ t).M2.obj T) (r3 : ∀ T, (KK κ t).M3.obj (S.obj T) →+ (KK κ t).M3.obj T), ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r1 T' ((KK κ t).M1.map (S.map φ) x) = (KK κ t).M1.map φ (r1 T x)) ∧ (∀ T x, r1 T ((KK κ t).M1.map (u.app T) x) = 0) ∧ (∀ T x, r1 T ((KK κ t).M1.map (v.app T) x) = x)) ∧ ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r2 T' ((KK κ t).M2.map (S.map φ) x) = (KK κ t).M2.map φ (r2 T x)) ∧ (∀ T x, r2 T ((KK κ t).M2.map (u.app T) x) = 0) ∧ (∀ T x, r2 T ((KK κ t).M2.map (v.app T) x) = x)) ∧ (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r3 T' ((KK κ t).M3.map (S.map φ) x) = (KK κ t).M3.map φ (r3 T x)) ∧ (∀ T x, r3 T ((KK κ t).M3.map (u.app T) x) = 0) ∧ (∀ T x, r3 T ((KK κ t).M3.map (v.app T) x) = x) := by
  first | exact @GlobalTheory.PDForm.Nbhd.exists_retraction | exact GlobalTheory.PDForm.Nbhd.exists_retraction | (intros; apply GlobalTheory.PDForm.Nbhd.exists_retraction <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C), A.dim = B.dim → B.dim = C.dim → (IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g) ∧ deg (f ≫ g) = deg f * deg g := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp | exact GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp <;> assumption)
end
