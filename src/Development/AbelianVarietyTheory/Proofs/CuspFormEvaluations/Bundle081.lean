module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle051
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle055
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle053
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle071
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle030
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle075
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBaseChangeEigenBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle023
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle020
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle025
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle026

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem AnFr.e_natCast_smul_eq_pow {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (z : Fin g → ℂ) (n : ℕ) : Φ.e ((n : ℂ) • z) = Φ.e z ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

theorem thValAt_eq_polyDeriv_fock : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ (n : ℕ) (x x2 : Fin n → Dw.La), (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ b, x2 b - x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v : ℂ, ThValAt Xo c nab y x P v → v = ((l.M : ℂ)⁻¹) ^ P.totalDegree * I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk (x2 b)) (fun w => θ ((l.M : ℂ) • w)) (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ _ y g ty el Φ mk hlat hlin hlev nab hnab θ hθ n x x2 hx2 hx a P hP v hv
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hM : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 l.odd.pos.ne'
  have hV := fun b => GlobalTheory.T.section_at_level_point_eq_translate_by_representative E H Dw l Xo c y g ty el Φ mk hlat hlin hlev θ hθ (x b) (x2 b) (hx2 b) (hx b)
  have hpow : ∀ b, Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk (x2 b)) ^ (l.M ^ 2) = 1 := by
    intro b
    rw [← Φ.toAnFr.e_natCast_smul_eq_pow, smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero 2 hM), one_smul]
    exact (Φ.e_ker _).2 (hlat _)
  have hex := fun b => (GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo l.M l.odd (ptO Xo y.x) y.s).1
    (KilledBy Xo (l.Mb ^ 2)) (levPt Xo y.x (x b)) _ (hV b).1.2 (hpow b) (hV b).1.1
  choose F hF using hex
  have hw : ThValAt Xo c nab y x P (thExpr Xo c nab y P F) :=
    ⟨ℂ, inferInstance, inferInstance, AlgHom.id c.F ℂ, y, F,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, GlobalTheory.FramedBaseChange.refl y, hF, rfl⟩
  have hvw : v = thExpr Xo c nab y P F :=
    GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hnab ℂ ℂ (AlgHom.id c.F ℂ) y y
      (GlobalTheory.FramedBaseChange.refl y) a n x P hP v _ hv hw
  have hN := GlobalTheory.T.harmonicValue_canonicalConnection_eq_polyDeriv hC E H Dw l Xo c y g ty el Φ nab hnab (l.M ^ 2) n F _
    (fun b => (hV b).2 (F b) (hF b)) a P hP.1
  rw [hvw, thExpr, map_inv₀, map_pow, map_natCast, ← inv_pow]
  exact congrArg _ hN

end GlobalTheory.AnVal
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_card_comp_le : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * Zb D large₂ ^ 2 := by
  intro D T h large₂ j hj w hP h2 hrn h16 σ hσ
  obtain ⟨hg, hlrd, hd, hcc, hf, -, -, -, hn⟩ := hP
  obtain ⟨-, -, -, -, -, hfd, hdE, -, -, -, hsk, hne, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L h2 hlrd hd hcc
  obtain ⟨AA, hFG, hA, hdual⟩ := GlobalTheory.T.principalDatum_fg_perfect_tracePairing D
  obtain ⟨-, -, hM, -, -, -, hJ⟩ := GlobalTheory.T.numerical_consequences_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hJ j hj
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hrL : Real.log D.R.r ≤ large₂.sc.L :=
    le_trans (Real.log_le_log (by exact_mod_cast hr) (by exact_mod_cast hrn)) hn
  have hML : Real.log T.Q.l.M' ≤ 30 * large₂.sc.L := by
    rw [hM, hMg]
    have h0 := hg 0
    have h1 := hg 1
    rcases Nat.eq_zero_or_pos (D.host.g 0) with a | a
    · rw [a]; simp; linarith
    rcases Nat.eq_zero_or_pos (D.host.g 1) with b | b
    · rw [b]; simp; linarith
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a.ne') (by exact_mod_cast b.ne')]
    linarith
  have key := GlobalTheory.log_card_comp_unf_le GlobalTheory.T.hasse_norm_theorem_quadratic_extension GlobalTheory.T.thetaUniformisation_complexAbelianVariety GlobalTheory.T.abelianScheme_laws_unconditional.1 D.host.E _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ))
    D.host.xi0 AA hsk hne hFG hA hdual large₂.sc.L (by rw [hfd]; exact_mod_cast h16) h2 hdE hrL
    (by rw [hfd]; exact_mod_cast hf) hML
  rw [hfd] at key
  exact key

end GlobalTheory.RunIn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thetaRule_mem_sec : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ thGen Xo c nab a n, f ∈ sec Xo c a n := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab a n f hf
  obtain ⟨x, P, hP, hR⟩ := hf
  unfold sec secW
  refine ⟨?_, ?_⟩
  · intro p q φ y z hyz
    exact (GlobalTheory.T.thetaValue_natural_algebraMap hL hC E H Dw l Xo c nab hnab p.R q.R φ y z hyz a n x P hP _ _ (hR p y) (hR q z)).symm
  · intro p t y y' hB
    have hid : FrMap (AlgHom.id c.F p.R) y' y' := by
      have hs : spMap (AlgHom.id c.F p.R).toRingHom = 𝟙 _ := by
        simp [spMap]
      have hd : spMap (dualMap (AlgHom.id c.F p.R).toRingHom) = 𝟙 _ := by
        have : dualMap (AlgHom.id c.F p.R).toRingHom = RingHom.id _ := by
          ext z <;> simp [dualMap]
        rw [this]
        simp [spMap]
      refine ⟨?_, ?_, 𝟙 _, ?_, ?_, ?_⟩
      · rw [hs, Category.id_comp]
      · intro τ i
        rw [hd, Category.id_comp]
      · simp
      · rw [hs]
        simp
      · intro i h
        have e : (Gx y'.x).presheaf.map (homOfLE h).op = 𝟙 _ := by
          erw [CategoryTheory.Functor.map_id]
        erw [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp, e]
        rfl
    have h1 := (GlobalTheory.T.thetaValue_weight_triangular_frame hL hC E H Dw l Xo c nab hnab p.R y y' t hB n a P).1 hP x (f p y) (hR p y)
    exact GlobalTheory.T.thetaValue_natural_algebraMap hL hC E H Dw l Xo c nab hnab p.R p.R (AlgHom.id c.F p.R) y' y' hid a n x P hP _ _ (hR p y') h1

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartFree

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped ComplexConjugate
open Matrix

theorem embeddings_differ_on_integer {E : Type} [Field E] [NumberField E] (τ τ' : E →+* ℂ) (h : τ ≠ τ') :
    ∃ a : 𝓞 E, τ (a : E) ≠ τ' (a : E) := by
  by_contra hall
  push Not at hall
  apply h
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  simp only [map_div₀]
  rw [show (algebraMap (𝓞 E) E a) = (a : E) from rfl, show (algebraMap (𝓞 E) E b) = (b : E) from rfl,
    hall a, hall b]

theorem balanced_pairs_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {d : ℕ} (A : 𝓞 E → Matrix (Fin d) (Fin d) S)
    (uvec : Lt1 Dw → Fin d → S)
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin d), ∑ j, A a i j * uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * uvec ℓ i)
    (M : Fin d → Fin d → S) (hbal : ∀ a, (A a).transpose * Matrix.of M = Matrix.of M * A (H.bar a))
    (ℓ ℓ' : Lt1 Dw) (hne : ∑ i, ∑ j, M i j * uvec ℓ i * uvec ℓ' j ≠ 0) :
    ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
  by_contra hc
  have hσ : ℓ.1 ≠ ComplexEmbedding.conjugate ℓ'.1 := by
    intro h
    apply hc
    rw [h]
    show ℓ'.1 = star (star ℓ'.1)
    rw [star_star]
  obtain ⟨a, ha⟩ := embeddings_differ_on_integer _ _ hσ
  have hmv : ∀ (b : 𝓞 E) (ℓ₀ : Lt1 Dw), A b *ᵥ uvec ℓ₀ = algebraMap c.F S (embK c ℓ₀.1 b) • uvec ℓ₀ := by
    intro b ℓ₀
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    exact heig b ℓ₀ i
  set B := uvec ℓ ⬝ᵥ (Matrix.of M *ᵥ uvec ℓ') with hB
  have hBe : B = ∑ i, ∑ j, M i j * uvec ℓ i * uvec ℓ' j := by
    rw [hB]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h1 := congrArg (fun N : Matrix (Fin d) (Fin d) S => uvec ℓ ⬝ᵥ (N *ᵥ uvec ℓ')) (hbal a)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hmv,
    hmv, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, ← hB] at h1
  have key : (algebraMap c.F S (embK c ℓ.1 a) - algebraMap c.F S (embK c ℓ'.1 (H.bar a))) * B = 0 := by
    rw [sub_mul, h1, sub_self]
  have hu : IsUnit (algebraMap c.F S (embK c ℓ.1 a) - algebraMap c.F S (embK c ℓ'.1 (H.bar a))) := by
    rw [← map_sub]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    intro h0
    apply ha
    have h2 := congrArg (fun x : c.F => (x : ℂ)) (sub_eq_zero.1 h0)
    simp only [embK_coe] at h2
    rw [h2, H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  exact hne (hBe ▸ (hu.mul_right_eq_zero).1 key)

theorem twist_on_eigenDirections (hFix : FrTruncFixSt) (hLE : LinEigSt) : FrTruncFixBSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
  obtain ⟨e', hfr, hrig, cc, hT, h0, hsym, hbal, hu⟩ := hFix E H Dw l Xo c hs S y C
  exact ⟨e', hfr, hrig, cc, hT, h0, hsym, fun m ℓ ℓ' hne => balanced_pairs_conjugate c (fun a => dLin (C.B.A.act a)) C.uvec
    (fun a ℓ i => hLE E H Dw l Xo c S y C a ℓ i) (cc m) (hbal m) ℓ ℓ' hne, hu⟩

theorem eigenDirections : LinEigSt := GlobalTheory.EigDir.linEig_holds

theorem chartIndep_of_globalFns (hGlob : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) : ChartIndepSt2 :=
  have hAct := expActOf_of eigenDirections
  chartIndep2_verb
    (chartIndepTrunc_of (expChartOf_of hAct) (ExpGauge.expGaugeOf_of hAct) tie_holds ExpUniqChart.expUniqTan
      (gaugeUniq_of_global hGlob) (killAddVal_of fun _ _ _ _ H => psiCover_holds H))
    (twist_on_eigenDirections (frTruncFix_of frRatio_holds) eigenDirections) germFix_holds (harmInv_of hAct)

theorem chartIndep : ChartIndepSt2 :=
  chartIndep_of_globalFns GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end GlobalTheory.ChartFree
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

namespace GlobalTheory

theorem framedPoint_bcGenR (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) : BcGenRSt Xo c := by
  intro p T _ _ ψ y
  obtain ⟨z, hx, -, pm, h1, h2, h3⟩ :=
    GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R T ψ y
  obtain ⟨x, _, _, _, _, _, s, gen⟩ := z
  dsimp only at hx pm h1 h2 h3
  subst hx
  have hpm : pm = _root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm ψ.toRingHom y.x := by
    apply pullback.hom_ext
    · exact h2.trans (_root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_fst _ _).symm
    · exact h1.trans (_root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_snd _ _).symm
  subst hpm
  exact ⟨s, h3, gen⟩

theorem framedPoint_baseChange_clauses :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), BcLieAnySt Xo c ∧ BcLieRSt Xo c ∧ BcGenRSt Xo c ∧ FrBCFieldSt Xo c := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨?_, ?_, framedPoint_bcGenR E H Dw l Xo c, ?_⟩
  · intro S _ _ K _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c S K ψ y τ w hw he
  · intro p T _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c p.R T ψ y τ w hw he
  · intro S _ _ y K _ _ ψ
    exact GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c S K ψ y

end GlobalTheory
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory

theorem cusp_readings_linearIndependent : ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt := by
  set_option synthInstance.maxHeartbeats 200000 in
  unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt
  intro D T h j hj ka σ hσ m f hf
  have hlin := hf.map' (T.C j ka).subtype (T.C j ka).ker_subtype
  have hmem : ∀ i, (f i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n := fun i =>
    Formalism.L2.Pj.cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n (f i).2
  have hU := h.unf j hj σ hσ
  have hB : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have key := (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (T.Q.Xo j) T.Q.c σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 hU)
    (wtA ka) ka.n).1 m (fun i => (f i : T.R j)) hmem hlin
  simp only [Formalism.L2.PjFree.rdU_ofPj] at key
  exact key

end GlobalTheory
end
