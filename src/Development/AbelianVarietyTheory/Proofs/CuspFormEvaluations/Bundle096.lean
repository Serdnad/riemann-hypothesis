module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle079
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle094
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogLeOfLePowMulPow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle047
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle050
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle053
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.shortGenerator_mem_span_small_supNorm_shortGenerators : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  first | exact @GlobalTheory.RunIn.sh_mem_span_small | exact GlobalTheory.RunIn.sh_mem_span_small | (intros; apply GlobalTheory.RunIn.sh_mem_span_small <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem exists_tiedW_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ThInt (recPJ h j hj) hinj EX wL → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → ∃ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw := by
  intro hC D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hP hR hI hG4 hPrw
  obtain ⟨hL, hf, hr, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR
  obtain ⟨hDF, hn, hrn, hLP⟩ :=
    (GlobalTheory.RunWeights.weights_below D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj.1 hP).1 wL (by simp)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hRL := GlobalTheory.pageRows_of_le D large₂ j ka wL hL0 hDF hn hR
  have hn0 : 0 < wL.n := by omega
  have hO : OPO large₂ (recB h.toLawsCore) := by
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -⟩, -⟩ := hP
    exact hO
  obtain ⟨N, w0, hspan, hN, hsup⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hC D T h hG large₂ j hj wL hRL hL hrn hLP
  have hcount := log_count_le_mul_size D _ large₂ j wL N Prw hL hn0 hRL hO hPrw hN
  have hs : (0 : ℝ) ≤ wL.size := by
    have h1 := frn_le_size_sub_one wL
    have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * wL.n := by positivity
    push_cast at h1
    linarith
  have hp : 0 ≤ Real.log (D.host.pde : ℝ) := Real.log_natCast_nonneg _
  have hZ : 0 ≤ Zb D large₂ := by unfold Zb; positivity
  have hnum := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j wL D.host.pde hL hn0).2.2
  have hGc := mul_le_mul_of_nonneg_right (hG4 D.host.pde (by simp)) hs
  have hd : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
    rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  have hK : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
  refine (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) N w0
    ((lamStar D + 2 * Real.log D.host.pde) * wL.size) _ Gc Prw (by positivity) (by positivity) (fun σ => ?_)
    hspan hsup (hnum.trans hGc)).2 hI hcount
  rw [sW_eq_sOf]
  refine ((GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D _ hinj EX j wL).2 σ).2.2.2.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hs

end GlobalTheory.RunIn
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem semilinear_eq_zero_of_span_smul {O K L M ι : Type} [CommRing O] [Field K] [Field L] [Algebra O K]
    [AddCommGroup M] [Module K M] [Module O M] [IsScalarTower O K M] (σ : K →+* L) (φ : M →ₛₗ[σ] L)
    (w : ι → M) (hw : ∀ i, φ (w i) = 0) (s : O) (hs : algebraMap O K s ≠ 0) (f : M)
    (hf : s • f ∈ Submodule.span O (Set.range w)) : φ f = 0 := by
  have h1 : ∀ g ∈ Submodule.span O (Set.range w), φ g = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hw i
    | zero => exact map_zero φ
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul a x _ hx => rw [← algebraMap_smul K a x, map_smulₛₗ, hx, smul_zero]
  have h2 := h1 _ hf
  rw [← algebraMap_smul K s f, map_smulₛₗ, smul_eq_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left ((map_ne_zero σ).2 hs)

theorem eq_zero_of_span_eq_WWc {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (w : WeightFamilies.Wt D j)
    {ι : Type} (g : ι → B.Cusp j w) (s : 𝓞 B.KO) (hs : s ≠ 0)
    (hg : Submodule.span (𝓞 B.KO) (Set.range g) = X.WWc s w) (σ : B.KO →+* ℂ) (φ : B.Cusp j w → ℂ)
    (hadd : ∀ F F', φ (F + F') = φ F + φ F') (hsmul : ∀ (a : B.KO) F, φ (a • F) = σ a * φ F)
    (h0 : ∀ i, φ (g i) = 0) (F : B.Cusp j w) (hF : F ∈ X.thAll w) : φ F = 0 := by
  have hW : s • F ∈ X.WWc s w := ⟨F, hF, rfl⟩
  rw [← hg] at hW
  exact semilinear_eq_zero_of_span_smul σ ⟨⟨φ, hadd⟩, hsmul⟩ g h0 s
    (fun h' => hs (RingOfIntegers.coe_eq_zero_iff.1 h')) F hW



theorem noCommonZero_of_tiedW : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → S.sW ≠ 0 → ∀ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW S Gc Prw → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) := by
  intro hC D T h EX j hj S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hP hs G hG
  obtain ⟨hDF, -, hr, hl⟩ := (GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hj.1 hP).1 wL (Set.mem_insert _ _)
  have hlp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj wL hl
  have hg : ∀ i, 2 * WeightAlgebra.DF ka + 2 < D.host.g i := hP.2.2.2.1.2.2.2.2.2
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hdeg : 4 * WeightAlgebra.DF wL + 4 ≤ T.Q.l.M := by
    have h1 : (2 * WeightAlgebra.DF ka + 3) * 3 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (hg 0) (by have := hg 1; omega)
    omega
  refine GlobalTheory.FrameZero.noCommonZero_of_readings D T h j hj (wtA wL) wL.n G.N _
    (fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j wL (G.w i).2)) fun k x hx => ?_
  obtain ⟨f, hf, hf0⟩ := GlobalTheory.noCommonZero_of_chartIndep hC D T h j hj wL hr hlp hdeg (half_level_generator_norm D T h EX) T.σ₀ T.good_σ₀ k x hx
  have hc : f ∈ cutR T.C j wL := by
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA wL) hlp f hf
  have hF : (⟨f, hc⟩ : (recB h.toLawsCore).Cusp j wL) ∈ (recPJ h j hj).thAll wL := Submodule.subset_span hf
  by_contra hno
  have hno' : ∀ i, rdU (T.U j T.σ₀) (G.w i).1 k x = 0 := fun i => by
    by_contra h'
    exact hno ⟨i, h'⟩
  have hadd : ∀ F F' : T.R j, rdU (T.U j T.σ₀) (F + F') k x = rdU (T.U j T.σ₀) F k x + rdU (T.U j T.σ₀) F' k x :=
    fun F F' => by rw [map_add (f := _)]; rfl
  have hsmul : ∀ (a : T.Q.c.F) (F : T.R j), rdU (T.U j T.σ₀) (a • F) k x = T.σ₀ a * rdU (T.U j T.σ₀) F k x :=
    fun a F => by rw [map_smulₛₗ]; rfl
  exact hf0 (eq_zero_of_span_eq_WWc (recPJ h j hj) wL G.w S.sW hs hG.1 T.σ₀
    (fun F => rdU (T.U j T.σ₀) F.1 k x) (fun F F' => hadd F.1 F'.1) (fun a F => hsmul a F.1) hno' ⟨f, hc⟩ hF)

end GlobalTheory.RunIn
end
