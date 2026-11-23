module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle054
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaSublatticeJetNeZero
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle074
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle063
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetTranslateProjectedVacuumLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle083
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle086
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle067
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle008
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle026
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle067
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
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
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem net_count_dim {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j} (Nt : NetNorms.NetData B j ka)
    (σ : B.KO →+* ℂ) (c : ℝ) (hM : NetNorms.NetMax Nt) (hS : NetNorms.NetSize Nt c) (hI : NetNorms.NetInj Nt σ) :
    Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ c ∧ ∀ n : ℕ, n ≤ Module.finrank B.KO (B.Cusp j ka) → Real.log n ≤ c := by
  have hlog16 : ∀ k : ℕ, Real.log (k : ℝ) ≤ Real.log (16 * (k : ℝ)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      exact Real.log_le_log hk' (by linarith)
  have hfirst : Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ c := (hlog16 _).trans (hS σ)
  refine ⟨hfirst, ?_⟩
  intro n hn

  have hdim : Module.finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hli := hI _ (Module.finBasis B.KO (B.Cusp j ka)) (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have hle := hli.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using hle
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hc : 0 ≤ Real.log (16 * (Fintype.card (Nt.NN σ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (Fintype.card (Nt.NN σ)) with h0 | h0
      · rw [h0]
        simp
      · apply Real.log_nonneg
        have : (1 : ℝ) ≤ Fintype.card (Nt.NN σ) := by exact_mod_cast h0
        linarith
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [hS σ]
  · calc Real.log (n : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := by
          apply Real.log_le_log (by exact_mod_cast hnpos)
          exact_mod_cast hn.trans hdim
      _ ≤ c := hfirst

theorem le_finrank_of_shareRd {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka : WeightFamilies.Wt D j)
    (N : Submodule (𝓞 B.KO) (B.Cusp j ka)) (Tn del : ℕ) (hT : WeightFamilies.dimY D j + 1 ≤ Tn)
    (hR : ShareRd (D := D) (j := j) Tn del (X.rk ka N)) : del ≤ Module.finrank B.KO (B.Cusp j ka) := by
  have hpos : 0 < Nat.choose (Tn - 1) (WeightFamilies.dimY D j) := Nat.choose_pos (by omega)
  have hc : (1 : ℝ) ≤ (Nat.choose (Tn - 1) (WeightFamilies.dimY D j) : ℝ) := by exact_mod_cast hpos
  have hR' : (Nat.choose (Tn - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ (X.rk ka N : ℝ) := hR
  have hdel0 : (0 : ℝ) ≤ del := by positivity
  have hdel : (del : ℝ) ≤ (X.rk ka N : ℝ) := by nlinarith

  have hrk : X.rk ka N ≤ Module.finrank B.KO (B.Cusp j ka) := Submodule.finrank_le _
  have hdel' : del ≤ X.rk ka N := by exact_mod_cast hdel
  exact hdel'.trans hrk


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem net_at_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ (Nt : NetNorms.NetData (recB h.toLawsCore) j ka) (σ₀ : (recB h.toLawsCore).KO →+* ℂ), NetNorms.NetMax Nt ∧ NetNorms.NetLeSup Nt ∧ NetNorms.NetPageG Nt large₂ 1041 3 ∧ NetNorms.NetInj Nt σ₀ ∧ Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ pdR large₂ ka ∧ DeepSubMul (recPJ h j hj) ∧ Real.log (Module.finrank (recB h.toLawsCore).KO ((recB h.toLawsCore).Cusp j ka) : ℝ) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ del : ℕ, LatAt (recB h.toLawsCore) j ka → ShareRd (D := D) (j := j) Tn del ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka)) → Real.log del ≤ 1041 * Zb D large₂ ^ 3 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  obtain ⟨hyp, page, _tie, _p13, _frd, r8, _df, ck⟩ := hP
  obtain ⟨hrows, hf⟩ := GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hyp page ck
  obtain ⟨hParA, hSetC, -, -, -⟩ := hyp
  obtain ⟨_Q, _PT, hSz, -, -⟩ := page
  obtain ⟨hL2, -⟩ := GlobalTheory.EtaAn.page_rows D large₂ H.CA hParA hSz
  obtain ⟨hkn, -, -, -, -, -, -, -, -, hnP, -, -, -, hnV, -, -, -, -, -, h40, -⟩ := hSetC
  have hfr : D.R.r ≤ D.R.f * D.R.r := Nat.le_mul_of_pos_left _ (by omega)
  have hr : D.R.r ≤ ka.n := by
    rw [hkn, hnV]
    have : D.R.f * D.R.r ≤ 8 * D.R.f * D.R.r := by
      rw [Nat.mul_assoc]
      omega
    omega
  have hZ : 1 ≤ Zb D large₂ := by
    have hf' : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hr' : (8 : ℝ) ≤ D.R.r := by exact_mod_cast r8
    have hfr' : (128 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    show 1 ≤ (D.R.f : ℝ) * D.R.r * large₂.sc.L
    nlinarith
  obtain ⟨Nt, hM, hLe, hS, hI⟩ := GlobalTheory.RunIn.NetAtRecord.netData_exists D T h
    (GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore) large₂ j hj ka hrows hL2 hr hf
  let σ₀ : (recB h.toLawsCore).KO →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ)).toRingHom
  obtain ⟨hcnt, hdim⟩ := net_count_dim Nt σ₀ _ hM hS (hI σ₀)
  have hpg := GlobalTheory.page_relation_deg_three D large₂ j ka 1041 3 le_rfl le_rfl hZ
  refine ⟨Nt, σ₀, hM, hLe, fun σ => (hS σ).trans hpg, hI σ₀, hcnt.trans hpg,
    (GlobalTheory.deepSubMul_rec_all D T h j hj).1, hdim _ le_rfl, ?_⟩
  intro del _hLat hR
  exact hdim _ (le_finrank_of_shareRd (recPJ h j hj) ka _ Tn del (by omega) hR)

end GlobalTheory.RunJoin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_theta_sublattice_jet_ne_zero_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) ∧ I2.polyDeriv P (letterDir X hr idx) F 0 ≠ 0 := by
  first | exact @GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero | exact GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero | (intros; apply GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.jet_translate_projected_vacuum_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ lam : ℝ, 0 < lam → (∀ u ∈ L, u ≠ 0 → lam ^ 2 ≤ (hx X bas idx x (pv X idx x u) (pv X idx x u)).re) → ∀ (y : Matrix (Fin n) (Fin r) E) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (d : ℕ), P.IsHomogeneous d → ‖κ * thP X hr bas idx (heisG X bas y (projA X bas (w : E) (tens Λ L) v)) P x‖ * Real.sqrt ((((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup) : ℝ) ^ r) ≤ (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * g * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (g * n) := by
  first | exact @GlobalTheory.Dict.VacJet.jet_projA_le | exact GlobalTheory.Dict.VacJet.jet_projA_le | (intros; apply GlobalTheory.Dict.VacJet.jet_projA_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaPt

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i

  simp only [dmin, lminor]
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

theorem sum_norm_coeff_rename_map {K α β : Type} [Field K] (σ : K →+* ℂ) (e : α ≃ β) (P : MvPolynomial α K) :
    ∑ m ∈ (MvPolynomial.rename e (MvPolynomial.map σ P)).support,
      ‖(MvPolynomial.rename e (MvPolynomial.map σ P)).coeff m‖ = ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := by
  classical
  rw [MvPolynomial.support_rename_of_injective e.injective,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective e.injective h]
  simp only [MvPolynomial.coeff_rename_mapDomain _ e.injective, MvPolynomial.coeff_map]
  rw [MvPolynomial.support_map_of_injective _ σ.injective]

theorem theta_bound_ortho : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n) := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hG hU hr1 t ht hc a n hDom _ nab hnab xx P hP f hf k x ho lam hlam hla

  have hunit : IsUnitFr (U.X k) x.1 := isUnitFr_of_isOrtho ho
  obtain ⟨W, Dc, A, θ, v, κ, hDe, hWg, hw0, hSD, hmark, hAm, hRead, hth1, hmean, hvac, hprod⟩ :=
    GlobalTheory.Dict.VSetup.exists_setup E H Dw l Xo c σ r U hG hU hr1 a n hDom k x hunit
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hn : Even n := hDom.2

  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Yr, hYr⟩ : ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E,
      IsRoots l (U.X k).Λ (W.mark k) l.M Y := by
    exact (DualMark.dual_marking E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hSD hmark
      (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  set Y := Yr fun b => (Submodule.Quotient.mk (xx b) : LevQ Dw l)
  have hY : ∀ b, (∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), a - xx b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
        Y b - ((l.M : E)⁻¹) • W.mark k a ∈ (U.X k).Λ) ∧
        ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ (U.X k).Λ, s • Y b = (2 * l.M) • u := by
    intro b
    obtain ⟨⟨a', ha', hq, hmem⟩, hj⟩ := hYr (fun b => (Submodule.Quotient.mk (xx b) : LevQ Dw l)) b
    exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hmem⟩, hj⟩

  have hval := (GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xx P hP).2 f hf ℂ (unC U k x)
  have hdir : ∀ ℓ, letterDir (U.X k) Dc.hr Dc.idx (Dc.eL ℓ) =
      Pi.single ℓ.2.2 (Pi.single (W.e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) := hDe ▸ Dc.dir_eq
  have heq := GlobalTheory.Dict.thVal_eq_thP hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ
    (unC U k x) A Dc.sympl x.2 hSD Dw.p n Dc.hr Dc.eL hU.1 hn hdir nab hnab θ v κ hRead hvac hprod
    (W.mark k) hmark hAm xx Y hY a P hP _ hval

  have hstd : stdL E n ∈ Vset E n 1 := Base.stdL_mem_Vset n 1
  have hint : IsIntegral ℤ ((H.w0 : 𝓞 E) : E) := (H.w0).isIntegral_coe
  have hproj : projA (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v = v := by
    rw [(GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn (H.w0 : E) hint hw0 (U.X k).Λ hSD 1
      (stdL E n) hstd).2.2.1 v hvac.1 v hvac, hvac.2.1, one_smul]

  have hlamL : ∀ u ∈ (U.X k).Λ, u ≠ 0 →
      lam ^ 2 ≤ (hx (U.X k) Dc.bas Dc.idx x.1 (pv (U.X k) Dc.idx x.1 u) (pv (U.X k) Dc.idx x.1 u)).re :=
    fun u hu hne => hla.trans ((GlobalTheory.Dict.hx_ortho E r (U.X k) W.g Dc.bas Dc.idx Dc.sympl x.1 x.2 ho).2.2.1 u hu hne)

  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).IsHomogeneous (DF Dw a) :=
    (((GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2 P
      (by unfold harmA at hP; unfold HaO at hP; exact hP.1)).map _).rename_isHomogeneous
  have hb := GlobalTheory.Dict.VacJet.jet_projA_le E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn H.w0 hw0
    (U.X k).Λ hSD (stdL E n) hstd v hvac x.1 x.2 ho t ht (hc k) θ κ hth1 hmean hprod lam hlam hlamL Y
    (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) (DF Dw a) hhom

  rw [hproj, AddSubgroup.relIndex_self, Nat.cast_one, one_pow, Real.sqrt_one, _root_.mul_one] at hb
  have hsum : ∑ m ∈ (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).support,
      ‖(MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).coeff m‖ =
        ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := sum_norm_coeff_rename_map σ Dc.eL P
  have hgR : ((W.g : ℕ) : ℝ) = ((fdeg E * r : ℕ) : ℝ) := by rw [hWg]
  have hgn : W.g * n = fdeg E * r * n := by rw [hWg]
  rw [hsum, hgR, hgn] at hb
  have hv0 : Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = evR Xo c f (unC U k x) := rfl
  rw [hv0, heq]
  exact hb

end GlobalTheory.Dict.ThetaPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def oneSim (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower _ _ _ _ _ := ⟨0, by simp⟩
  inv _ _ := ⟨LinearMap.id, fun _ => ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩⟩
  mult _ _ _ _ := by simp

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem evR_eq_of_point_eq (d : DeltaDat Xo c n) {ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ} (hψ : d.PsiTie ψ)
    {k : Type} [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y y' : FrPt d.Xo₂ d.c₂ k) (h : y'.x = y.x) :
    evR d.Xo₂ d.c₂ d.cδ y' = evR d.Xo₂ d.c₂ d.cδ y := by
  have e := hψ 1 (oneSim Dw) (Iso.refl _)
    ⟨by simp [oneSim], fun a => by simp [oneSim], fun a => ⟨0, by simp [oneSim]⟩⟩
    (fun a => ⟨0, by simp [oneSim]⟩)
    ⟨Category.id_comp _, GlobalTheory.LevelTwist.sabMapId _,
      fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
      fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩
    (fun _ => rfl) k y y' (h.trans (Category.comp_id _).symm)
  simpa using e

theorem map_wchar {J : Type} [Fintype J] {K S T : Type} [Field K] [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (χ : S →ₐ[K] T) (e : J → ℕ) (t : J → Sˣ) :
    χ (wchar e t) = wchar e (fun i => Units.map (χ : S →* T) (t i)) := by
  simp [wchar, map_prod, map_pow]

end GlobalTheory.ShortDescent

namespace GlobalTheory


open ShortDescent in
theorem shortValTot_of_pinned : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) → AllTest Xo c → EvalWD (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) → AllTest d.Xo₂ d.c₂ → d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ShortValTot Xo c nab bad nV a n d := by
  intro hL hC E _ _ _ H Dw l Xo c n d hN _ hAll hW₂ hAll₂ hLev hA hnab hpin nab bad nV a Λ N x0 P hU _ hT hO hX hP
  obtain ⟨_, hnab⟩ := hnab
  obtain ⟨hle, hmap⟩ := GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d
  have hpin' := hpin (hle _ _ hX)
  have hP₂ := hmap a P hP.1
  obtain ⟨hex, -⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hT hO a _ hP₂ (d.w x0)
    (d.eF (betaH (Dw := Dw) c Λ))
  have hd := GlobalTheory.T.evaluation_lemma_for_nabla_levels hL hC E H Dw l Xo c n d hW₂ hAll₂ hN hLev hA hnab hpin' Λ N hU hT hO a _ hP₂ x0
    (d.eF (betaH (Dw := Dw) c Λ))
  obtain ⟨hlift, -, hbor⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d
  obtain ⟨_, ψ, _, -, hψ⟩ := hpin'
  refine ⟨hex, fun p y => (hd p y).exists.choose, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, ?_⟩
  · refine (hd q z).unique (hd q z).exists.choose_spec ?_
    intro k _ _ _ _ hk χ w w₂ hw ho v hv
    exact (hd p y).exists.choose_spec k hk (χ.comp φ) w w₂ (GlobalTheory.FramedBaseChange.trans φ χ h hw) ho v hv
  · refine (hd p y').unique (hd p y').exists.choose_spec ?_
    intro k _ _ _ _ hk χ w' w₂' hw' ho' v' hv'
    obtain ⟨w, hw⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χ y
    have hb := frBorBC _ _ χ t y y' w w' h hw hw'
    obtain ⟨w₂, hx₂, ho⟩ := hlift k hk w w₂'.x (ho'.1.trans hb.1) w₂'.x_over
    have hb₂ := hbor k hk _ w w' w₂ w₂' ho ho' hx₂.symm hb
    obtain ⟨v, hv, -⟩ := hex k w₂
    have hv₂ := (GlobalTheory.thetaValue_weight hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab k w₂ w₂' _ hb₂ n a _).2 hP₂
      _ Λ _ N v hv
    have e := (hd p y).exists.choose_spec k hk χ w w₂ hw ho v hv
    rw [(hex k w₂').unique hv' hv₂, map_mul, map_wchar, evR_eq_of_point_eq d hψ w₂ w₂' hx₂.symm]
    refine (congrArg (_ * ·) e).trans ?_
    ring
  · intro k _ _ _ _ hk y y₂ ho
    obtain ⟨v, hv, -⟩ := hex k y₂
    refine ⟨v, hv, ?_⟩
    have hy := hAll k y
    unfold evR evalAt
    rw [dite_eq_left hy]
    exact (hd _ _).exists.choose_spec k hk _ y y₂ hy.choose_spec.choose_spec.choose_spec ho v hv

end GlobalTheory
end
end
