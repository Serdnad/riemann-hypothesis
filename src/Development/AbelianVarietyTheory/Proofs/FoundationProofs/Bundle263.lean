module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficients
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle258
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
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

theorem _root_.GlobalTheory.T.siegel_unit_q_expansion_coefficients : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b : ℕ), 0 < M → a < M → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → Ω), GlobalTheory.QFam.HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => ε (A n)) ∧ (∀ n : ℕ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff (((k : ℚ) + n) / M) = A n) ∧ ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r = 0 := by
  first | exact @GlobalTheory.KExp.siegel_exp | exact GlobalTheory.KExp.siegel_exp | (intros; apply GlobalTheory.KExp.siegel_exp <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

theorem _root_.GlobalTheory.T.siegelUnitInTower_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ), admitted c x → siegel T c x ≠ 0 := by
  first | exact @GlobalTheory.KZ.siegel_ne_zero | exact GlobalTheory.KZ.siegel_ne_zero | (intros; apply GlobalTheory.KZ.siegel_ne_zero <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

theorem _root_.GlobalTheory.T.siegelUnitInTower_sl_action_rowVector : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  first | exact @GlobalTheory.KZ.SiegelSL.sl_siegel | exact GlobalTheory.KZ.SiegelSL.sl_siegel | (intros; apply GlobalTheory.KZ.SiegelSL.sl_siegel <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem adjoint_U : ∀ (k L N l : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → l.Prime → l ∣ L → ¬ l ∣ N → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (Uo l a)) = pet k ρ (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) (qs a) := by
  intro k L N l ε ρ h a hk hL hNL hl hlL hlN hW hh ha
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNL hL
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hpos : 0 < l := hl.pos
  obtain ⟨-, hUa⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hpos ha.1
  have hcontH : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have hcontA : Continuous (qs a) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha.1).2
  have hModA : Mod (qs a) := GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1
  have hdet : ∀ j : Fin l, (repU l j).det = l := by
    intro j; simp [repU, Matrix.det_fin_two]
  have hint : ∀ i : Fin l, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repU l i) (qs a) τ * (τ.im : ℂ) ^ k)) := by
    intro i
    have hd : 0 < (repU l i).det := by rw [hdet]; exact_mod_cast hpos
    exact GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ _ hk hL hNL hW hh
      (((GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk).2.2.2.1 _ hd hcontA).aestronglyMeasurable)
      ((GlobalTheory.T.hasModerateGrowth_algebra_slash_stable).2.2 (qs a) k _ hd (by simp [repU]) hModA)
  have key := GlobalTheory.T.petersson_doubleCoset_adjoint k L N l ε ρ (DU L l) (Fin l) (Fin l) (repU l)
    (fun j => (repL L l (some j)).adjugate) (qs h) (qs a) hk hN hNL hpos hcop hW
    (by
      intro δ hδ
      obtain ⟨h1, h2, -⟩ := hδ
      exact ⟨h1, (Int.natCast_dvd_natCast.2 hNL).trans h2⟩)
    ((GlobalTheory.T.heckeU_leftRepresentatives_level_change L l hl).1 hlL) (GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU L l hL hl hlL) hh.1.2 ha.2 hcontH hcontA hint
  have e1 : qs (Uo l a) = hsum k (ch ε) (repU l) (qs a) := by
    funext τ
    rw [hUa τ]
    simp [hsum, repU, ch]
  have e2 : (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) =
      (fun τ => ∑ j, ch ε⁻¹ ((fun j => (repL L l (some j)).adjugate) j 0 0) *
        slz k ((fun j => (repL L l (some j)).adjugate) j).adjugate (qs h) τ) := by
    funext τ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [repL, ch, Matrix.adjugate_fin_two_of]
  rw [e1, e2]
  exact key

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma adjT_adj_adj (M : M2) : M.adjugate.adjugate = M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]

lemma intMatrixTwo_adjugate_zero_zero (M : M2) : M.adjugate 0 0 = M 1 1 := by
  simp [Matrix.adjugate_fin_two]

lemma pet_const_mul_left (k : ℕ) (ρ : ℍ → ℝ) (c : ℂ) (F G : ℍ → ℂ) :
    pet k ρ (fun τ => c * F τ) G = conj c * pet k ρ F G := by
  unfold pet
  rw [← integral_const_mul]
  congr 1; funext τ
  simp only [map_mul]; ring

end GlobalTheory.EisM

theorem GlobalTheory.EisM.pet_To_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → q.Prime → ¬ q ∣ L → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (To k (ch ε q) q a)) = ch ε q * pet k ρ (qs (To k (ch ε q) q h)) (qs a) := by
  intro k L N q ε ρ h a hk hL hNL hq hqL hρ hh ha
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNL hL
  have hqN : ¬ q ∣ N := fun h' => hqL (h'.trans hNL)
  have hcop : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN
  have hq0 : 0 < q := hq.pos
  have hε1 : ch ε 1 = 1 := by simp [ch]
  obtain ⟨-, hTaeq⟩ := GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k q (ch ε) a hk hq0 hε1 ha.1
  obtain ⟨-, hTheq⟩ := GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k q (ch ε) h hk hq0 hε1 hh.1.1
  have hcont_h := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have hcont_a := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha.1).2
  have hslz := GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk
  have hdetpos : ∀ i, 0 < (repT q i).det := by
    intro i; cases i <;> simp [repT, repU, Matrix.det_fin_two_of, hq0]
  have hlow : ∀ i, (repT q i) 1 0 = 0 := by
    intro i; cases i <;> simp [repT, repU]
  have hint : ∀ i, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repT q i) (qs a) τ * (τ.im : ℂ) ^ k)) :=
    fun i => GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ (slz k (repT q i) (qs a)) hk hL hNL hρ hh
      ((hslz.2.2.2.1 _ (hdetpos i) hcont_a).aestronglyMeasurable)
      (GlobalTheory.T.hasModerateGrowth_algebra_slash_stable.2.2 _ k _ (hdetpos i) (hlow i) (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1))
  have hadj := GlobalTheory.T.petersson_doubleCoset_adjoint k L N q ε ρ (DT L q) (Option (Fin q)) (Option (Fin q)) (repT q)
    (fun i => (repT q i).adjugate) (qs h) (qs a) hk hN hNL hq0 hcop hρ
    (fun δ hδ => ⟨hδ.1, (Int.natCast_dvd_natCast.2 hNL).trans hδ.2⟩)
    (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL) (GlobalTheory.T.rightGamma0CosetDecomposition_adjugate_heckeT L q hq hqL) hh.1.2 ha.2 hcont_h hcont_a hint
  rw [← hTaeq] at hadj
  rw [hadj]

  have hu : ((q : ℤ) : ZMod N) = ((ZMod.unitOfCoprime q hcop : (ZMod N)ˣ) : ZMod N) := by
    simp [ZMod.coe_unitOfCoprime]
  have hnorm : ‖ch ε q‖ = 1 := by
    simp only [ch]; rw [hu]; exact DirichletCharacter.unit_norm_eq_one ε _
  have hne : ch ε q ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hinvq : ch ε⁻¹ q = (ch ε q)⁻¹ := by
    simp only [ch]; rw [MulChar.inv_apply_eq_inv']
  have hinv1 : ch ε⁻¹ 1 = 1 := by simp [ch]
  have hsumeq : (fun τ => ∑ j, ch ε⁻¹ ((repT q j).adjugate 0 0) * slz k (repT q j).adjugate.adjugate (qs h) τ)
      = fun τ => (ch ε q)⁻¹ * qs (To k (ch ε q) q h) τ := by
    funext τ
    rw [hTheq]
    simp only [hsum, Fintype.sum_option, adjT_adj_adj, intMatrixTwo_adjugate_zero_zero, Finset.mul_sum, mul_add]
    simp [repT, repU, hinvq, hinv1, hε1, hne]
  rw [hsumeq, pet_const_mul_left]
  have hc : conj ((ch ε q)⁻¹) = ch ε q := by
    rw [map_inv₀]
    have : conj (ch ε q) * ch ε q = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]; simp
    exact inv_eq_of_mul_eq_one_right this
  rw [hc]
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.torsion_kaehler_span_dlog_indep : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ z qn zi qi : integralClosure (O0 p) Ω,
  (z : Ω) = T.ζ n → (qn : Ω) = T.qq n → z * zi = 1 → qn * qi = 1 →
  (∀ η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω), (p ^ n : ℕ) • η = 0 →
     ∃ x y : integralClosure (O0 p) Ω, (p ^ c : ℕ) • η =
       (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn) ∧
  (∀ x y : integralClosure (O0 p) Ω,
     (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn = 0 →
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * x = (p : integralClosure (O0 p) Ω) ^ (n - 1) * t) ∧
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * y = (p : integralClosure (O0 p) Ω) ^ n * t)) := by
  first | exact @GlobalTheory.K5.TorsionDiff.torsion_span_and_indep | exact GlobalTheory.K5.TorsionDiff.torsion_span_and_indep | (intros; apply GlobalTheory.K5.TorsionDiff.torsion_span_and_indep <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_local_conjugation_selfDual_lattices_host : ∀ (D : D7) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L), ∃ γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram, {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v := by
  first | exact @GlobalTheory.LocalConjugacy.exists_local_conjugation | exact GlobalTheory.LocalConjugacy.exists_local_conjugation | (intros; apply GlobalTheory.LocalConjugacy.exists_local_conjugation <;> assumption)
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

noncomputable section

namespace GlobalTheory.UnitaryTheta.Graph

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def term (H : Sesq V) (a : V ≃ₗ[ℂ] V) (α : V → ℂ) (x z : V) : ℂ :=
  α x * kerTerm H x (a z) z * cexp (-(π : ℂ) * H z z)

theorem term_eq (H : Sesq V) (a : V ≃ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) (α : V → ℂ) (x y z : V)
    (hy : y - a y = x) :
    term H a α x z = α x * cexp (-(π : ℂ) * H x x / 2) *
      cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z (-(a.symm x))) := by
  have h1 : H z (a.symm x) = H (a z) x := by rw [← ha, LinearEquiv.apply_symm_apply]
  rw [term, kerTerm, hy, mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [map_add (f := _), map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply, h1]
  ring

theorem value_eq (H : Sesq V) (hH : IsPosHerm H) (a : V ≃ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) (x y : V)
    (hy : y - a y = x) :
    cexp (-(π : ℂ) * H x x / 2) * cexp (π * H y (-(a.symm x))) =
      cexp (-((π : ℂ) * I) * ((H y x).im : ℂ)) := by
  have h1 : H y (a.symm x) = H y x - H x x := by
    rw [← ha, LinearEquiv.apply_symm_apply]
    have : a y = y - x := by rw [← hy]; abel
    rw [this]; simp
  have h2 : H x x = H y x + conj (H y x) := by
    rw [← hH.1, ← hy]
    simp only [map_sub, LinearMap.sub_apply, ha]
    ring
  rw [← Complex.exp_add]
  congr 1
  rw [map_neg, h1, h2, Complex.im_eq_sub_conj]
  have := Complex.I_ne_zero
  field_simp
  ring

theorem term_shift (H : Sesq V) (hH : IsPosHerm H) (a : V ≃ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w)
    (Λ : AddSubgroup V) (α : V → ℂ) (hα : IsSemichar H Λ α) (x y z : V) (hx : x ∈ Λ) (hy : y ∈ Λ)
    (hay : a y ∈ Λ) (hαy : α (a y) = α y) :
    term H a α (x - (y - a y)) z = term H a α x (z + y) := by
  have hx' : x - (y - a y) ∈ Λ := Λ.sub_mem hx (Λ.sub_mem hy hay)
  have e1 := hα.2.2 _ hx' _ hy
  have e2 := hα.2.2 _ hx _ hay
  have e0 : x - (y - a y) + y = x + a y := by abel
  rw [e0, e2, hαy] at e1
  have hne : α y ≠ 0 := by rcases hα.1 y hy with h | h <;> simp [h]
  have e3 : α (x - (y - a y)) = α x * cexp (-((π : ℂ) * I) * ((H x (a y)).im : ℂ)
      + ((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ)) := by
    have h := Complex.exp_ne_zero (-((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ))
    apply mul_right_cancel₀ h
    apply mul_right_cancel₀ hne
    rw [mul_assoc (α x), ← Complex.exp_add]
    have : -((π : ℂ) * I) * ((H x (a y)).im : ℂ)
      + ((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ) + -((π : ℂ) * I) * ((H (x - (y - a y)) y).im : ℂ) =
        -((π : ℂ) * I) * ((H x (a y)).im : ℂ) := by ring
    rw [this]
    linear_combination -e1
  obtain ⟨m, hm⟩ := hα.2.1 x hx _ hay
  have hm' : ((H x (a y)).im : ℂ) = m := by exact_mod_cast hm
  rw [term, term, e3, kerTerm, kerTerm]
  simp only [mul_assoc, ← Complex.exp_add]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-m, ?_⟩
  push_cast
  rw [← hm']
  simp only [Complex.im_eq_sub_conj, ← hH.1]
  simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, ha]
  have := Complex.I_ne_zero
  field_simp
  ring

end Alg

theorem ph_real (κ : ℝ) : GlobalTheory.Phase.Ph (κ : ℂ) :=
  ⟨2, two_pos, by rw [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]⟩

theorem ph_det_mul_integral : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (a : V ≃ₗ[ℂ] V), (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ.FG → Λ' ≤ Λ → (Λ'.addSubgroupOf Λ).FiniteIndex → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → GlobalTheory.Phase.Ph (LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * ∫ z in Fd, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet Λ Λ' _ hfg hle hfi haΛ α hα hαa Fd hFd
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable Λ' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨κ, -, hg⟩ := GlobalTheory.T.integral_cexp_herm_gaussian_eq_div_det V μ H hH a ha hdet
  let E := LinearMap.equivOfDetNeZero _ hdet
  have hE : ∀ x, E x = x - a x := fun x => rfl
  let B : V →ₗ[ℂ] V := E.symm
  have hB1 : ∀ x, B x - a (B x) = x := fun x => by rw [← hE]; exact E.apply_symm_apply x
  have hB2 : ∀ x, B (x - a x) = x := fun x => by rw [← hE]; exact E.symm_apply_apply x
  obtain ⟨M, _, s, hs, huniq, hph⟩ := GlobalTheory.T.unitary_finite_gaussSum_phase_rootOfUnity V H hH a ha B hB1 hB2 Λ Λ' hfg hle hfi haΛ α hα hαa
  have hint : ∀ x, Integrable (term H a α x) μ := fun x => by
    have : term H a α x = _ := funext fun z => term_eq H a ha α x (B x) z (hB1 x)
    rw [this]
    exact (hg (B x) _).1.const_mul _
  have hval : ∀ x, ∫ z, term H a α x z ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) *
      (α x * cexp (-((π : ℂ) * I) * ((H (B x) x).im : ℂ))) := fun x => by
    simp only [fun z => term_eq H a ha α x (B x) z (hB1 x)]
    rw [integral_const_mul, (hg (B x) _).2, ← value_eq H hH a ha x (B x) (hB1 x)]
    ring
  let f : M × Λ' → Λ := fun p => ⟨s p.1 - ((p.2 : V) - a p.2),
    Λ.sub_mem (hs _) (Λ.sub_mem (hle p.2.2) (haΛ _ p.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      exact (huniq _ (f p).2).unique rfl (congrArg Subtype.val hpq)
    · intro x
      obtain ⟨p, hp, -⟩ := huniq x x.2
      exact ⟨p, Subtype.ext hp.symm⟩
  have hsum : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) =
      ∑ m, ∑' y : Λ', term H a α (s m) (z + y) := fun z => by
    have h1 : Summable (fun x : Λ => term H a α x z) :=
      ((GlobalTheory.T.heisenbergReproducingKernelSum_spec V H hH Λ α hα).1 (a z) z).mul_right _
    have h2 := (Equiv.ofBijective f hf).summable_iff.2 h1
    rw [kerSum, ← tsum_mul_right]
    change ∑' x : Λ, term H a α x z = _
    rw [← (Equiv.ofBijective f hf).tsum_eq]
    refine (h2.tsum_prod).trans ?_
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun m _ => tsum_congr fun y => ?_
    exact term_shift H hH a ha Λ α hα (s m) y z (hs m) (hle y.2) (haΛ _ y.2) (hαa _ y.2)
  have hu := fun m => GlobalTheory.T.setIntegral_tsum_translate_eq_integral V μ Λ' Fd hFd _ (hint (s m))
  simp only [hsum]
  rw [integral_finsetSum _ (fun m _ => (hu m).1)]
  simp only [fun m => (hu m).2, hval]
  rw [← Finset.mul_sum, ← mul_assoc, mul_div_cancel₀ _ hdet]
  exact (ph_real κ).mul hph

end GlobalTheory.UnitaryTheta.Graph
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem relIndex_ne_zero_of_denom {A ι κ : Type} [CommRing A] [Finite ι] [Finite κ] (S : Subring A) (I : AddSubgroup A) (k n : ℕ)
    (hk : IsUnit (k : A)) (hfin : Finite (S ⧸ Ideal.span {((k * n : ℕ) : S)})) (hn : ∀ s ∈ S, (n : A) * s ∈ I)
    (L T : AddSubgroup (Matrix ι κ A)) (hL : ∀ ζ : Matrix ι κ A, (∀ i j, ζ i j ∈ I) → ζ ∈ L)
    (hT : ∀ ζ ∈ T, ∀ i j, (k : A) * ζ i j ∈ S) : L.relIndex T ≠ 0 := by
  let φ : T →+ (ι → κ → S ⧸ Ideal.span {((k * n : ℕ) : S)}) :=
    AddMonoidHom.mk' (fun ζ i j => Ideal.Quotient.mk _ ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩) (fun x y => by
      funext i j
      rw [Pi.add_apply, Pi.add_apply, ← map_add (f := _)]
      congr 1
      exact Subtype.ext (mul_add _ _ _))
  have hle : φ.ker ≤ L.addSubgroupOf T := by
    intro ζ hζ
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hL _ fun i j => ?_
    have h0 : Ideal.Quotient.mk (Ideal.span {((k * n : ℕ) : S)}) ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩ = 0 :=
      congrFun (congrFun ((AddMonoidHom.mem_ker).1 hζ) i) j
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : (s : A) * (((k * n : ℕ) : S) : A) = (k : A) * ζ.1 i j := congrArg Subtype.val hs
    have h2 : ζ.1 i j = (n : A) * s := by
      apply hk.mul_left_cancel
      rw [← h1]
      push_cast
      ring
    rw [h2]
    exact hn _ s.2
  have : φ.ker.FiniteIndex := AddSubgroup.finiteIndex_ker φ
  exact (AddSubgroup.finiteIndex_of_le hle).index_ne_zero

theorem idx_latA_ne_zero : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m : ℕ), 0 < m → ∀ T : Submodule (𝓞 D.host.E) (XA D N N'), (∀ ζ ∈ T, m • ζ ∈ latA D cc N N') → idx (latA D cc N N') T ≠ 0 := by
  intro D hD cc δ hc N N' m hm T hT
  obtain ⟨-, -, -, -, ⟨m₁, hm₁, h₁⟩, m₂, hm₂, h₂⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'
  have hk : 0 < m₁ * m := Nat.mul_pos hm₁ hm
  have hu : IsUnit ((m₁ * m : ℕ) : AE D) := by
    have := (IsUnit.mk0 ((m₁ * m : ℕ) : D.host.E) (Nat.cast_ne_zero.2 hk.ne')).map (inc D)
    rwa [map_natCast] at this
  refine relIndex_ne_zero_of_denom (OhE D) (IhE D cc) (m₁ * m) m₂ hu
    (GlobalTheory.HeckeVal.finite_quot D _ (Nat.mul_pos hk hm₂)) h₂ _ _ (fun ζ h => mem_latA.2 h) fun ζ hζ i j => ?_
  have h := h₁ _ (mem_latA.1 (hT ζ hζ) i j)
  rw [Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc] at h
  rwa [Nat.cast_mul]

end GlobalTheory.FinWeil
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.padicModel_equation_tangent_at_latticeParameter : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → wpD g.abelian₂ v ∈ Qbar → g.W.toAffine.Equation (GlobalTheory.EvenTheta.xAt g v) (GlobalTheory.ThetaPar.yAt g v) ∧ 2 * GlobalTheory.ThetaPar.yAt g v + g.W.a₁ * GlobalTheory.EvenTheta.xAt g v + g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * lamC g.lam (wpD g.abelian₂ v) := by
  first | exact @GlobalTheory.ThetaPar.ModelPoint.model_point | exact GlobalTheory.ThetaPar.ModelPoint.model_point | (intros; apply GlobalTheory.ThetaPar.ModelPoint.model_point <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.padicModel_tangentLaw_at_double : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → 2 * P ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → 2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃ ≠ 0 ∧ GlobalTheory.EvenTheta.xAt g (2 * P) = ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) ^ 2 + g.W.a₁ * ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) - g.W.a₂ - 2 * GlobalTheory.EvenTheta.xAt g P := by
  first | exact @GlobalTheory.ModelDouble.tangent_law | exact GlobalTheory.ModelDouble.tangent_law | (intros; apply GlobalTheory.ModelDouble.tangent_law <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.padicModel_chordLaw_sum_and_difference : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P Q : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → Q ∉ g.abelian₂ → P + Q ∉ g.abelian₂ → P - Q ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → wpF g.abelian₂ Q ∈ Qbar → wpD g.abelian₂ Q ∈ Qbar → GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) = ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P - Q) = ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  first | exact @GlobalTheory.ThetaPar.Chord.model_chord | exact GlobalTheory.ThetaPar.Chord.model_chord | (intros; apply GlobalTheory.ThetaPar.Chord.model_chord <;> assumption)
end
