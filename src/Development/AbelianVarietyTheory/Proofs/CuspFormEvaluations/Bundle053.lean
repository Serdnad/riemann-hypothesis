module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle058
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionAtLevelPointEqTranslateByRepresentative
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle051
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle035
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.CuspDataBounds

theorem exists_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (X : Data E r)
    (hX : Xx.toData = X) (S : Set E)
    (hΛ : Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ Xx.L', v = a • u})
    (NA NC : ℕ) (hA : 0 < NA) (hC : 0 < NC) (hAi : ∀ a ∈ S, IsIntegral ℤ ((NA : E) * a)) (hCS : (NC : E) ∈ S) :
    ∃ e : XExt X, e.NA = NA ∧ e.NC = NC ∧ e.g = Xx.g ∧ e.k0 = Xx.k0 := by
  subst hX
  refine ⟨⟨Xx.k0, Xx.minWeight_pos, Xx.k0_le, Xx.ξ0_abs, Xx.EF_int, Xx.EF_perf, Xx.L', Xx.L'_fg, Xx.L'_int,
      Xx.L'_dual, NA, NC, hA, hC, ?_, ?_, Xx.g, Xx.g_pos, Xx.cong⟩, rfl, rfl, rfl, rfl⟩
  ·
    intro x hx
    rw [hΛ] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hy
      rw [smul_smul]
      have h1 : ((NA : E) * a) • u = (⟨(NA : E) * a, hAi a ha⟩ : 𝓞 E) • u := by
        rw [← algebraMap_smul E (⟨(NA : E) * a, hAi a ha⟩ : 𝓞 E) u]
        rfl
      rw [h1]
      exact Xx.L'.smul_mem _ hu
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact Xx.L'.add_mem hy hz
    | smul c y _ hy =>
      rw [smul_comm]
      exact Xx.L'.smul_mem c hy
  ·
    intro x hx
    rw [hΛ]
    exact Submodule.subset_span ⟨(NC : E), hCS, x, hx, rfl⟩

theorem weight_bounds (L f r n d : ℝ) (hL : 2 ≤ L) (hf : 1 ≤ f) (hfr : f ≤ r) (hrn : r ≤ n) (hd : 0 ≤ d)
    (hn : Real.log n ≤ L) (hD : Real.log (1 + d) ≤ 2 * L) :
    Real.log (d + f * n + 1) ≤ 3 * L ∧ Real.log (f * (d + f * n + 1) + 2) ≤ 5 * L ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ d + f * r * n / 2 → Real.log (1 + s) ≤ 3 * L := by
  have hx3 : 3 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e2 : Real.exp (2 * L) = Real.exp L ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp (3 * L) = Real.exp L ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have e5 : Real.exp (5 * L) = Real.exp L ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  set x := Real.exp L with hx
  have hn0 : 0 < n := by linarith
  have hnx : n ≤ x := (Real.log_le_iff_le_exp hn0).1 hn
  have hdx : 1 + d ≤ x ^ 2 := by rw [← e2]; exact (Real.log_le_iff_le_exp (by linarith)).1 hD
  have hfx : f ≤ x := by linarith
  have hrx : r ≤ x := by linarith
  have hfn : f * n ≤ x ^ 2 := by nlinarith
  have hfn0 : 0 ≤ f * n := by nlinarith
  have hx2 : 9 ≤ x ^ 2 := by nlinarith
  have hx23 : 3 * x ^ 2 ≤ x ^ 3 := by nlinarith
  have hx35 : 9 * x ^ 3 ≤ x ^ 5 := by nlinarith
  have hA : d + f * n + 1 ≤ 2 * x ^ 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.log_le_iff_le_exp (by linarith), e3]
    linarith
  · have hB : f * (d + f * n + 1) ≤ x * (2 * x ^ 2) := mul_le_mul hfx hA (by linarith) (by linarith)
    rw [Real.log_le_iff_le_exp (by nlinarith), e5]
    nlinarith
  · intro s hs0 hs
    have hfr0 : 0 ≤ f * r := by nlinarith
    have hC : f * r * n ≤ x ^ 3 := by
      have h1 : f * r ≤ x * x := mul_le_mul hfx hrx (by linarith) (by linarith)
      have h2 : f * r * n ≤ x * x * x := mul_le_mul h1 hnx hn0.le (by positivity)
      nlinarith
    rw [Real.log_le_iff_le_exp (by linarith), e3]
    nlinarith

private theorem level_M_eq_g_zero_mul_g_one_of_lawsM {D : D7} (T : Core D) (h : Formalism.L2.Pj.LawsM T) :
    T.Q.l.M = D.host.g 0 * D.host.g 1 := by
  have p := h.pins.2.1
  unfold Formalism.L2.Pj.Par.PinLevel at p
  exact p.1

theorem cusp_data_bounds : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (e : ∀ k : (T.U j σ).Comp, XExt ((T.U j σ).X k)) (M wg : ℝ), 1 ≤ M ∧ Real.log M ≤ 30 * large₂.sc.L ∧ 0 < wg ∧ Real.log wg ≤ 3 * large₂.sc.L ∧ Real.log ((fdeg D.host.E : ℝ) * wg + 2) ≤ 5 * large₂.sc.L ∧ ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ wg ∧ (∀ v ∈ (e k).L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j σ).X k).Γ, ((T.U j σ).X k).χ (laU (T.U j σ) (wtA w) w.n k) γ = 1 ∧ ∀ τ : ((T.U j σ).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j σ).X k).flowMat v τ ((M : ℂ) * τ.1 b)) ∧ Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L ∧ Real.log (e k).NA ≤ 4 * large₂.sc.L ∧ Real.log (e k).NC ≤ 2 * large₂.sc.L ∧ Real.log (e k).g ≤ 19 * large₂.sc.L ∧ Real.log (1 / (e k).k0) ≤ 3 * large₂.sc.L := by
  intro D T h hGam large₂ j hj w hP hL hrn σ hσ
  obtain ⟨hgi, hlrd, hdd, hcc, -, -, -, hDF, hn⟩ := hP
  obtain ⟨⟨NA, hNA0, hNAi, hNAL⟩, hccA, hcc0, ⟨m, hm0, hmi, hmL⟩, hk0L, hfdeg, -, -, hfr, hf1, hxicc, -,
    hxiabs⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hlrd hdd hcc
  have h10 := GlobalTheory.T.modelWeight_size_spread_bound D T h j hj w σ hσ
  obtain ⟨hW1, hW2, hW3⟩ := weight_bounds large₂.sc.L (D.R.f : ℝ) (D.R.r : ℝ) (w.n : ℝ) (WeightAlgebra.DF w : ℝ) hL
    (by exact_mod_cast hf1) (by exact_mod_cast hfr) (by exact_mod_cast hrn) (by positivity) hn hDF
  have hwg0 : 0 < (WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1 := by positivity
  have hwgF : Real.log ((fdeg D.host.E : ℝ) * ((WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1) + 2) ≤ 5 * large₂.sc.L := by
    rw [hfdeg]; exact hW2
  have hspread : ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤
      (WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1 := fun k => by linarith [(h10 k).1]
  have hla : ∀ k, Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L :=
    fun k => hW3 _ (by positivity) (h10 k).2
  rcases isEmpty_or_nonempty (T.U j σ).Comp with hE | ⟨⟨k₁⟩⟩
  · exact ⟨fun k => isEmptyElim k, 1, _, le_rfl, by simp; positivity, hwg0, hW1, hwgF, fun k => isEmptyElim k⟩
  have hPr : GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M :=
    fun k γ h1 h2 => hGam j hj σ hσ k γ h1 h2
  choose Xx hXx hXg hXΛ hXk0 hXNA hXNC using GlobalTheory.T.exists_rankOneCuspLatticeData_of_principal D T.toCore h.toLawsCore j hj σ hσ hPr
  choose e heNA heNC heg hek0 using fun k => exists_ext (Xx k) _ (hXx k) _ (hXΛ k) NA
    (Ideal.absNorm D.host.ccK) hNA0 hcc0 hNAi hccA
  have hMpos : 0 < T.Q.l.M := by rw [← hXg k₁]; exact (Xx k₁).g_pos
  have hlev : T.Q.l.M = D.host.g 0 * D.host.g 1 := level_M_eq_g_zero_mul_g_one_of_lawsM T.toCore h.toLawsCore.toLawsM

  have hgL : Real.log (T.Q.l.M : ℝ) ≤ 19 * large₂.sc.L := by
    have h0 : D.host.g 0 ≠ 0 := fun h0 => by simp [hlev, h0] at hMpos
    have h1 : D.host.g 1 ≠ 0 := fun h1 => by simp [hlev, h1] at hMpos
    rw [hlev, Nat.cast_mul, Real.log_mul (by exact_mod_cast h0) (by exact_mod_cast h1)]
    linarith [hgi 0, hgi 1]

  have hmX : ∀ k, IsIntegral ℤ ((m : D.host.E) * (2 * ((T.U j σ).X k).ξ0)) := by
    intro k
    rcases GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq D.host.E D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
      hxicc ((T.U j σ).X k).ξ0_im (by rw [hxiabs, h.xiAbs j hj σ hσ k]) with h1 | h1
    · rw [h1]; exact hmi
    · rw [h1]; convert hmi.neg using 1; ring
  have hMk : ∀ k, ((e k).toX.g * (e k).toX.NA * (e k).toX.NC * m : ℕ) =
      T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m := by
    intro k
    show (e k).g * (e k).NA * (e k).NC * m = _
    rw [heg, heNA, heNC, hXg]
  have hM1 : 1 ≤ T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hMpos hNA0) hcc0) hm0
  refine ⟨e, ((T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m : ℕ) : ℝ), _, by exact_mod_cast hM1, ?_, hwg0, hW1,
    hwgF, fun k => ⟨hspread k, ?_, hla k, ?_, ?_, ?_, ?_⟩⟩
  · push_cast
    have hN : (0 : ℝ) < NA := by exact_mod_cast hNA0
    have hC : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hcc0
    have hm : (0 : ℝ) < m := by exact_mod_cast hm0
    have hg : (0 : ℝ) < T.Q.l.M := by exact_mod_cast hMpos
    rw [Real.log_mul (by positivity) hm.ne', Real.log_mul (by positivity) hC.ne',
      Real.log_mul hg.ne' hN.ne']
    linarith
  · intro v hv hv0 b hb hbi
    obtain ⟨γ, hγ, hγf⟩ := GlobalTheory.TransvLevel.transv_mem D.host.E D.R.r (e k).toX m (hmX k) v hv hv0 b hb hbi
    refine ⟨γ, hγ, h.chiTriv j hj σ hσ _ _ (Formalism.L2.Pj.dom_wtA w) k γ hγ, fun τ => ?_⟩
    have := hγf τ
    rw [hMk k] at this
    exact this
  · rw [heNA]; exact hNAL
  · rw [heNC]; exact hcc
  · rw [heg, hXg]; exact hgL
  · rw [hek0, hXk0]; exact hk0L

end GlobalTheory.CuspDataBounds
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

theorem _root_.GlobalTheory.T.connectionPolynomialExpression_coeffFieldExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (nab : NabV Xo c) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (k : ℤ) (F : Fin n → LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), (MvPolynomial.map (incF c c' hle) P).totalDegree = P.totalDegree ∧ ∑ m ∈ (MvPolynomial.map (incF c c' hle) P).support, algebraMap c'.F S ((MvPolynomial.map (incF c c' hle) P).coeff m) * ∏ b, nabBC hle nab y k (F b) (colOf m b) = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab (y.res hle h) k (F b) (colOf m b) := by
  first | exact @GlobalTheory.FieldBC.polyNab_fieldBC | exact GlobalTheory.FieldBC.polyNab_fieldBC | (intros; apply GlobalTheory.FieldBC.polyNab_fieldBC <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

private theorem log_norm_sOf_eq_DF_log_add_log_pPow (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (sOf B hinj EX w : B.KO)‖ =
      (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
        Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) := by
  obtain ⟨hnn, hlog⟩ := GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ
  have hp := ((GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w).2.2.2.2.2 (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)).1
  have hσ : σ (sOf B hinj EX w : B.KO) = σ (nnW B hinj EX w : B.KO) *
      (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℂ) := by
    unfold sOf
    push_cast
    rw [map_mul, map_natCast]
  have hne : σ (nnW B hinj EX w : B.KO) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hnn
  have hpne : ((pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℕ) : ℝ) ≠ 0 := by
    have : 0 < pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) := hp
    positivity
  rw [hσ, norm_mul, Complex.norm_natCast, Real.log_mul (norm_ne_zero_iff.mpr hne) hpne, hlog]

theorem sOf_ne_zero_and_log_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j), sOf B hinj EX w ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, 0 ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ≤ lamStar D * w.size := by
  intro D B hinj EX j w
  obtain ⟨_, _, hB0, hA0, hP, hpp⟩ := GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w
  obtain ⟨hp1, hplog⟩ := hpp (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)
  have hlp0 : 0 ≤ Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hlpB : Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) ≤
      ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    rw [hplog]; exact hP
  have hDF : (0 : ℝ) ≤ WeightAlgebra.DF w := Nat.cast_nonneg _

  have hsz : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size := by
    have key : w.size = (WeightAlgebra.DF w : ℝ) +
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 := by
      unfold WeightFamilies.Wt.size WeightAlgebra.DF WeightAlgebra.degP
      push_cast
      ring
    have : (0 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      positivity
    linarith

  have hqq : Real.log (qq D : ℝ) ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rcases Nat.eq_zero_or_pos (qq D) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; exact hA0
    · have h0 : qq D ≤ D.host.g 0 := min_le_left _ _
      have h1 : qq D ≤ D.host.g 1 := min_le_right _ _
      have hle : qq D ≤ D.host.g 0 * D.host.g 1 :=
        h0.trans (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le h h1))
      have hcast : (qq D : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by exact_mod_cast hle
      exact Real.log_le_log (by exact_mod_cast h) hcast
  refine ⟨?_, fun σ => ?_⟩
  · unfold sOf
    refine mul_ne_zero ?_ ?_
    · obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
      exact (GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ).1
    · have : pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) ≠ 0 := by omega
      exact_mod_cast this
  · rw [log_norm_sOf_eq_DF_log_add_log_pPow D B hinj EX j w σ]
    have hA : (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D : ℝ) ≤
        (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hqq (by positivity)
    have hA1 : 0 ≤ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by positivity
    have hL : lamStar D = Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
        Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := rfl
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    calc (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
          Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ)
        ≤ ((WeightAlgebra.DF w : ℝ) + 1) * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
            Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) := by
          nlinarith [mul_nonneg hDF hA0]
      _ ≤ w.size * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
            Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) :=
          mul_le_mul_of_nonneg_right hsz (by linarith)
      _ = lamStar D * w.size := by rw [hL]; ring

end GlobalTheory.RunIn
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) (X : PJ D B P j) (E : PtExt X)
  (hM : IntAtExt X E)

abbrev xN : PJ D n.base P j := PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM)

def globalFamilyDataBaseChange {ka wL wF : WeightFamilies.Wt D j} (G : EtaleWeightGaps.GlobalFamilyData X ka wL wF) : EtaleWeightGaps.GlobalFamilyData (xN n X E hM) ka wL wF where
  N := G.N
  w := G.w
  del := G.del
  th' := G.th'
  rz := G.rz
  alz := G.alz
  th0 := G.th0
  zc := G.zc
  rq := G.rq
  th := G.th
  iet := G.iet
  et := G.et
  mx := G.mx

end General

end GlobalTheory.RunIn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.section_at_level_point_eq_translate_by_representative : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ x x2 : Dw.La, x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) → x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) → (KilledBy Xo (l.Mb ^ 2) (Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2)) ∧ Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x) ∧ ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)), IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F → Φ.toAnFr.Rd ((l.M : ℤ) ^ 2) F (fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk x2) fun z => θ ((l.M : ℂ) • z)) := by
  first | exact @GlobalTheory.AnVal.rd_vt_levPt | exact GlobalTheory.AnVal.rd_vt_levPt | (intros; apply GlobalTheory.AnVal.rd_vt_levPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem sum_support_natCast_smul {σ K : Type} [Field K] [Algebra K ℂ] (N : ℕ) (P : MvPolynomial σ K)
    (hs : ((N : K) • P).support = P.support) (v : (σ →₀ ℕ) → ℂ) :
    ∑ m ∈ ((N : K) • P).support, algebraMap K ℂ (((N : K) • P).coeff m) * v m =
      (N : ℂ) * ∑ m ∈ P.support, algebraMap K ℂ (P.coeff m) * v m := by
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, map_natCast, _root_.mul_assoc]

theorem harm_nab_eq_polyDeriv : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : Fin n → (Fin g → ℂ) → ℂ), (∀ b, Φ.toAnFr.Rd k (F b) (θ b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, θ b (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ _ y g ty el Φ nab hnab k n F θ hθ a P hP
  classical
  obtain ⟨N, hN, hNP, hs⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := hnab.2 ℂ y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  obtain ⟨C, hd, hh, hF, hu, hgerm⟩ := GlobalTheory.T.exists_analytic_biextension_chart_complex_point E H Dw l Xo c y g ty el Φ hnab.1
  subst hd
  have hdiff : ∀ b, Differentiable ℂ (θ b) := fun b =>
    ((GlobalTheory.T.section_reading_existsUnique_isTheta _ _ _ _ _ Φ.toAnFr k (F b)).2.1 (θ b) (hθ b)).1
  have hg : ∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (tay (θ b) 0) := fun b => by
    have h := hgerm k (F b) (θ b) (hθ b)
    have e : (fun p : Fin 1 × Fin C.d => (p.1, Fin.cast (rfl : C.d = C.d).symm p.2)) = id := rfl
    simp only [e, MvPowerSeries.rename_id, AlgHom.id_apply] at h
    exact h
  have h := hC E H Dw l Xo c hnab.1 ℂ y C₁ C k n F f₁ (fun b => tay (θ b) 0) hf₁ hg a _ hNP
  unfold chartVal at h
  rw [sum_support_natCast_smul N P hs, sum_support_natCast_smul N P hs] at h
  have h' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hN.ne' : (N : ℂ) ≠ 0) h
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal ℂ C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  simp only [e₁]
  rw [h']
  have huu : C.uvec = fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ) := by
    funext ℓ i
    rw [hu ℓ i, Pi.single_apply]
    rfl
  have hpd := GlobalTheory.T.polyDeriv_prod_column_functions (Fin C.d → ℂ) (E →+* ℂ) Dw.mult n
    (fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ)) θ hdiff
    (MvPolynomial.map (algebraMap c.F ℂ) P)
  refine Eq.trans ?_ hpd.symm
  rw [MvPolynomial.support_map_of_injective P (algebraMap c.F ℂ).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [hh, huu]
  exact nabVal_additive C.B hF H.w0 k ((GlobalTheory.SCV.contDiff_of_differentiable (hdiff b) _).contDiffAt) _ _

end GlobalTheory.AnVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_translation_sections_universal_object : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)), (∀ (ok : (T ⟶ Xo.univ.t.G) → Prop) (t t' : T ⟶ Xo.univ.t.G), t' ^ N = t → t' ^ (N ^ 2) = 1 → ok t' → ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F) ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → ∃! F, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F := by
  first | exact @GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver | exact GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver | (intros; apply GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.exists_biextension_chart_with_germs_framed_point : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S), ∃ C : ChartAt Xo c y, FrTruncC y C ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f := by
  first | exact @GlobalTheory.ChartRing.exists_chartAt_with_germs | exact GlobalTheory.ChartRing.exists_chartAt_with_germs | (intros; apply GlobalTheory.ChartRing.exists_chartAt_with_germs <;> assumption)
end
