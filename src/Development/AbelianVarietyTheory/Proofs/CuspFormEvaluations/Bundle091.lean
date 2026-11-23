module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle075
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle063
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle090
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle083
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle037
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle130
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.ThetaNoZero

theorem mem_mul_smul_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R}
    (h : I ⊔ J = ⊤) {x : M} (hI : x ∈ I • (⊤ : Submodule R M)) (hJ : x ∈ J • (⊤ : Submodule R M)) :
    x ∈ (I * J) • (⊤ : Submodule R M) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)
  have e : x = i • x + j • x := by rw [← add_smul, hij, one_smul]
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hi hJ
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hj hI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dmin_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold dmin lminor psgn
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, Complex.ofReal_prod,
    ← Fin.prod_univ_eq_prod_range fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)]
  rfl

theorem psgn_mul_self (p i : ℕ) : psgn p i * psgn p i = 1 := by
  unfold psgn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold FD.sgn
  split_ifs <;> simp

theorem isUnitFr_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  rw [dmin_of_isOrtho ho, Complex.norm_real, Real.norm_eq_abs]
  have h := psgn_mul_self X.p0 i
  rcases mul_self_eq_one_iff.1 h with h | h <;> simp [h]

theorem rmul_mem_dom_of_isOrtho {X : Data E r} {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (ho : X.IsOrtho (rmul x b)) : rmul x b ∈ X.dom := by
  refine fun τ => ⟨?_, fun i => ?_⟩
  · change (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_of_isOrtho ho, Complex.ofReal_re, psgn_mul_self]
    exact one_pos

theorem mark_sub_mem {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {L : Lt E r}
    {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : IsMark l L mk) {a a' : Dw.La}
    (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) (ha' : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (h : a' - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ((l.M : E)⁻¹) • mk a' - ((l.M : E)⁻¹) • mk a ∈ L := by
  have h1 := mem_mul_smul_top l.coprime h (Submodule.sub_mem _ ha' ha)
  rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨z, -, hz⟩ := h1
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  rw [← smul_sub, ← map_sub, ← hz, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul,
    inv_mul_cancel₀ hM, one_smul]
  exact hm.mem z

theorem exists_thGen_rdU_ne_zero : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → 3 * Formalism.L2.Pj.DF Dw a + 2 ≤ l.M → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ k, ∀ x ∈ (U.X k).dom, ∃ f ∈ thGen Xo c nab a n, Formalism.L2.PjFree.rdU U f k x ≠ 0 := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hσ hU hr t ht hc a n hdom hrn hM _ nab hnab k x hx
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨x₀, b, hb, ho, rfl⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r (U.X k).p0 (U.X k).Ψ
    (U.X k).Gm (U.X k).Gm_herm).1 x hx
  have ho : (U.X k).IsOrtho (rmul x b) := ho
  have hx₀ := rmul_mem_dom_of_isOrtho hx hb ho
  obtain ⟨⟨P, hP, hP0⟩, hhom⟩ : (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ _ :=
    ⟨(GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).1 hdom (hrpq ▸ hrn),
      (GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2⟩
  have hdeg : P.totalDegree ≤ Formalism.L2.Pj.DF Dw a := (hhom P hP.1).totalDegree_le
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W, Dc, A, θ, v, κ, he, -, hw, hsd, hmk, hmarked, hreads, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr a n hdom k ⟨rmul x b, hx₀⟩ (isUnitFr_of_isOrtho ho)
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 hM0
  obtain ⟨-, -, hconj, hmul, hroots⟩ := GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM0)
  obtain ⟨Y, hY⟩ := hroots n l.M (Nat.pos_of_ne_zero hM0)
  have hQ0 : MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P) ≠ 0 := by
    intro h0
    refine hP0 (MvPolynomial.map_injective (algebraMap c.F ℂ) (algebraMap c.F ℂ).injective
      (MvPolynomial.rename_injective _ Dc.eL.injective ?_))
    rw [h0, map_zero, map_zero]
  have hQd : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).totalDegree ≤
      Formalism.L2.Pj.DF Dw a :=
    (((hhom P hP.1).map (algebraMap c.F ℂ)).rename_isHomogeneous (f := Dc.eL)).totalDegree_le
  obtain ⟨y, hy, hne⟩ := GlobalTheory.T.exists_level_translate_jet_ne_zero_alt E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 H.w0 hw
    (U.X k).Λ hsd (rmul x b) hx₀ ho t ht (hc k) (Mfr l) l.M l.odd (by rw [hconj, hmul]) v hvac θ κ hth hmean hprod
    _ hQ0 (by omega)
  choose xs hxs u hu hyx using fun j => hmk.surj _ (hy j)
  obtain ⟨⟨f, hf, hfs⟩, hev⟩ := GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xs P hP
  have hval := GlobalTheory.T.thetaValue_standardLattice_eq_classicalTheta hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e (rmul x b) (U.X k).Λ
    (unC U k ⟨rmul x b, hx₀⟩) A Dc.sympl hx₀ hsd Dw.p n Dc.hr Dc.eL hrpq hdom.2 (he ▸ Dc.dir_eq) nab hnab θ v κ
    hreads hvac hprod (W.mark k) hmk hmarked xs (Y fun j => Submodule.Quotient.mk (xs j))
    (fun j => by
      obtain ⟨⟨a', ha', hq, hYa⟩, hj⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
      exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hYa⟩, hj⟩)
    a P hP _ (hev f hf ℂ (unC U k ⟨rmul x b, hx₀⟩))
  have hne' := hne (Y fun j => Submodule.Quotient.mk (xs j)) fun j => by
    obtain ⟨⟨a', ha', hq, hYa⟩, -⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
    have h1 := mark_sub_mem hmk (hxs j) ha' ((Submodule.Quotient.eq _).1 hq)
    have h2 : y j = ((l.M : E)⁻¹) • W.mark k (xs j) + u j := by
      have := congrArg (fun z => ((l.M : E)⁻¹) • z) (hyx j)
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hME, one_smul, ← Nat.cast_smul_eq_nsmul E l.M (u j)] at this
      exact this
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hYa h1) (hu j)
    convert h3 using 1
    rw [h2]
    abel
  rw [← hval] at hne'
  refine ⟨f, ⟨xs, P, hP, hf⟩, fun h0 => hne' ?_⟩
  have hB := (hU.2.2.2.2.1 a n hdom f hfs k).2.1 x hx b hb
  rw [h0, mul_zero] at hB
  have e : Formalism.L2.PjFree.rdU U f k (rmul x b) = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨rmul x b, hx₀⟩)) := dif_pos hx₀
  exact e.symm.trans hB

end GlobalTheory.ThetaNoZero
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegreeInterpolationBounds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem totalDegree_eq_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = Formalism.L2.Pj.DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = Formalism.L2.Pj.DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Formalism.L2.Pj.DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  apply le_antisymm
  · exact Finset.sup_le fun m' hm' => (key m' hm').le
  · exact (key m hm) ▸ MvPolynomial.le_totalDegree hm

theorem pow_le_sq_of_log {M x : ℝ} {d : ℕ} (hM : 1 < M) (hd : 1 ≤ d) (hx : 0 ≤ x)
    (h : (d : ℝ) / 2 * Real.log M ≤ Real.log x) : M ^ d ≤ x ^ 2 := by
  have hl : 0 < Real.log M := Real.log_pos hM
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero] at h
      nlinarith
    · exact h0
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  linarith

theorem i2iAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → _root_.GlobalTheory.BlockTh.IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  intro hCI D T h EX j hj K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hTie hPage hSupp P₁ hP hB N w hC
    tableLineDegreeFive hP14
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  obtain ⟨α, hα1, hα2⟩ := GlobalTheory.RunIn.half_level_generator_norm D T h EX
  obtain ⟨hrun, hcc, -, -⟩ := GlobalTheory.T.thetaRunParameters_at_typePrimes_product D _ _ j (recPJ h j hj) K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hHP hTie hPage hSupp
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hP0 : P₁ ≠ 0 := fun e => GlobalTheory.BlockThInhab.not_isBlockProd_zero (T.Q.Dw j) wL.n T.Q.c.F (e ▸ hB)
  have hdeg : P₁.totalDegree = WeightAlgebra.DF wL :=
    (totalDegree_eq_DF T.Q.c hP hP0).trans (GlobalTheory.WeightExponents.weight_exponents D T.Q h.pins j hj wL).1
  have hq : (T.Q.Dw j).q ≤ D.R.m := by
    rw [(h.pins.2.2.2 j hj).2.1]
    exact Nat.sub_le _ _
  have hs : ∀ σ : T.Q.c.F →+* ℂ,
      (T.Q.l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F)‖ ^ 2 := by
    intro σ
    have h3 : (3 : ℝ) ≤ T.Q.l.M := by exact_mod_cast T.Q.l.three_le
    refine pow_le_sq_of_log (by linarith) (by rw [hdeg]; have := hSupp.2.2.2.2; omega) (norm_nonneg _) ?_
    rw [hdeg, hM, Nat.cast_mul]
    exact hSupp.2.1 σ
  have key := GlobalTheory.T.integralityBound_of_family_containing_scaled_thetaRules hCI D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D) (T.nab j) hnab
    (fun σ hσ => ⟨h.unf j hj σ hσ, h.unTest j hj σ hσ, h.xiAbs j hj σ hσ⟩) α hα1 hα2 (wtA wL) wL.n P₁ (dom_wtA wL) hP hB
    _ hs N (fun k => ((w k).1 : T.R j)) (fun k => cusp_le_sec _ _ _ _ _ (cutR_le T.C j wL (w k).2)) hC
    (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m (by rw [hdeg, hM]; exact hrun) (Or.inr hq) tableLineDegreeFive
    (cc D large₂ C2 A2 CR wL) hP14 (by rw [hM]; exact hcc)
  rw [hdeg, hM] at key
  exact key

end GlobalTheory.DegreeInterpolationBounds
end
end
