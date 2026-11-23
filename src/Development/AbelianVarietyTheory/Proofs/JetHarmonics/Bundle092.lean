module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle087
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle086
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.PeriodIntegrals.Bundle018
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle077
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle088
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle004
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TotalDegreeEqOfMemHarmA
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDmonOfEigen
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThirdPointDerivativeAtZeroSeriesMemIntegral
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.smoothVectors_discreteSeries_glModule : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  first | exact @GlobalTheory.smooth_gl_module | exact GlobalTheory.smooth_gl_module | (intros; apply GlobalTheory.smooth_gl_module <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.operatorEab_preserves_smooth_classCC : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (A : ℝ) (a b : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (B.CkOn ⊤ (B.GV k r) (Q.EH k r a b f) ∧ ∀ m : ℕ, B.InCC (A) m (Q.EH k r a b f)) := by
  first | exact @GlobalTheory.EabClass.eh_class | exact GlobalTheory.EabClass.eh_class | (intros; apply GlobalTheory.EabClass.eh_class <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.UnipotentRadicalHaar

theorem eq_smul_of_twoSided {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : B.IsHaarOn U ν) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ μ = c • ν := by
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν.finite_compact K hK⟩
  obtain ⟨c, -, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique hU hμ
    (ν := ν) ⟨inferInstance, hν.ne_zero, hν.conc, hν.left⟩
  exact ⟨c, c1, e⟩

theorem unimodular_normal : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → PI.IsRightInvM (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsFiniteMeasure μW ∧ PI.IsRightInvM (Formalism.QuantumDeterminants.Nset k r) μN ∧ (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, h * m * h⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) ∧ ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, μN.map (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h * Matrix.of x * h⁻¹) i j : Formalism.QuantumDeterminants.Mt k r)) = μN := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨νW, hνW⟩ := P.weyl_haar_exists k r z hz hT
  obtain ⟨νN, hνN⟩ := P.unipotent_haar_exists k r
  obtain ⟨a, a1, ea⟩ := eq_smul_of_twoSided (P.B2x3.closedW k r z) hW hνW
  obtain ⟨b, -, eb⟩ := eq_smul_of_twoSided (P.B2x2.closedN k r) hN hνN
  refine ⟨fun s hs => ?_, ⟨?_⟩, fun s hs => ?_,
    fun h hh m hm => (Formalism.QuantumDeterminants.uWNormal k r z hz h hh m hm).1, fun h hh => ?_⟩
  · rw [ea, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [PI.rmulQ, Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (a • ·) (hνW.right s hs)
  · have hK : IsCompact (Formalism.QuantumDeterminants.UWset k r z) := P.weyl_subgroup_compact k r z hz hT
    have h1 : νW (Formalism.QuantumDeterminants.UWset k r z) < ⊤ := hνW.finite_compact _ hK
    have h2 : νW Set.univ ≤ νW (Formalism.QuantumDeterminants.UWset k r z) + νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    have h3 : νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ = 0 := hνW.conc
    rw [h3, add_zero] at h2
    rw [ea, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top a1.lt_top (h2.trans_lt h1)
  · rw [eb, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [PI.rmulQ, Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (b • ·) (hνN.right s hs)
  · rw [eb, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (b • ·) (P.b2_conjInvRaw_proof k r z νN hz hT hνN h hh)

end GlobalTheory.UnipotentRadicalHaar
end

section

open Formalism.REAL

namespace GlobalTheory

theorem comatrix_last_row_inverts_casimir
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ)
    (hE : GlRel E) (hdet : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v)
    (hOm : ∀ y b, Om y b = ∑ c, E c b (y c)) :
    ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V),
      (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧
      ∀ u v, K u (PiLp.single 2 (Fin.last n) v) =
        qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by
  let Q : ℂ → Fin (n + 1) → Module.End ℂ V := fun u l =>
    (((-1 : ℤ) ^ (n + (l : ℕ)) : ℤ) : Module.End ℂ V) *
      qminor E Fin.castSucc (Fin.succAbove l) (u - 1)
  let K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V) := fun u =>
    ∑ l, (Q u l) ∘ₗ (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) l)
  have hK : ∀ u x, K u x = ∑ l, Q u l (x l) := by
    intro u x
    simp only [K, LinearMap.sum_apply, LinearMap.comp_apply, PiLp.projₗ_apply]
  refine ⟨K, fun u x => ?_, fun u v => ?_⟩
  · have h1 : ∀ l, ((u - 0) • x + Om x) l = ∑ c, Tm E u c l (x c) := by
      intro l
      simp only [Tm, sub_zero, PiLp.add_apply, PiLp.smul_apply, hOm, LinearMap.add_apply,
        Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single l]
      · simp
      · intro c _ hc
        simp [hc]
      · simp
    rw [hK]

    simp only [h1, map_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ c, ∑ l, Q u l (Tm E u c l (x c)) =
        (if c = Fin.last n then qdet E u else 0 : Module.End ℂ V) (x c) := by
      intro c
      rw [← capelli_comatrix_last_row _ n E hE u c, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Q, Module.End.mul_apply]
    simp only [h2]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [hdet]
    · intro c _ hc
      simp [hc]
    · simp
  · rw [hK, Finset.sum_eq_single (Fin.last n)]
    · have h3 : qminor E Fin.castSucc Fin.castSucc (u - 1) =
          qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) := by
        simp only [qdet, qminor, Tm, id, Fin.castSucc_inj]
      have h4 : ((-1 : ℤ) ^ (n + n)) = 1 := by
        rw [← two_mul, pow_mul]; simp
      simp only [Q, Fin.succAbove_last, h3, Fin.val_last, h4, Int.cast_one, one_mul,
        PiLp.single_eq_same]
    · intro c _ hc
      simp [PiLp.single_eq_of_ne, hc]
    · simp

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NabUniqCompare

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem pderiv_swap {σ R : Type} [CommRing R] (i j : σ) (P : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), hp, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem isHarmonic_iff_cmType {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) :
    IsHarmonic c P ↔ P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) := by
  have e : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ↔
      ∀ τ : E →+* ℂ, InPsi H τ → ∀ (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
    simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker, lap,
      LinearMap.sum_apply, LinearMap.smul_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  rw [e]
  refine ⟨fun h τ _ => h τ, fun h τ => ?_⟩
  by_cases hτ : InPsi H τ
  · exact h τ hτ
  · have key : ∀ σ : E →+* ℂ, σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) →
        ∀ (i : Fin (Dw.mult σ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (⟨σ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
      rintro σ rfl i i'
      rw [← h _ ((GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff τ).2 hτ) i' i]
      exact Finset.sum_congr rfl fun b _ => pderiv_swap _ _ _
    exact key τ (by ext x; simp)

def IsTopHarmonic {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  IsHarmonic c P ∧ RowInv Dw.mult n c.F P ∧
    ∃ a : (E →+* ℂ) × ℕ → ℕ, RowDeg Dw.mult n c.F (fun τ i => a (τ, i)) P

theorem mem_harmA_iff {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) :
    P ∈ harmA c a n ↔ IsHarmonic c P ∧ RowInv Dw.mult n c.F P ∧
      RowDeg Dw.mult n c.F (fun τ i => a (τ, i)) P ∧ ∀ m, IsIntegral ℤ (P.coeff m) := by
  rw [isHarmonic_iff_cmType]
  exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

def colSumL {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S) :
    MvPolynomial (LtN Dw n) c.F →ₗ[c.F] S :=
  (MvPolynomial.basisMonomials (LtN Dw n) c.F).constr c.F fun m => ∏ b : Fin n, v b (colOf m b)

theorem colSumL_apply {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S)
    (P : MvPolynomial (LtN Dw n) c.F) : colSumL c v P = colSum c v P := by
  conv_lhs => rw [P.as_sum]

  rw [map_sum, colSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (MvPolynomial.monomial m (P.coeff m) : MvPolynomial (LtN Dw n) c.F) =
      P.coeff m • MvPolynomial.basisMonomials (LtN Dw n) c.F m := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, colSumL, Module.Basis.constr_basis, Algebra.smul_def]

def UniqueOn (Q : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k n : ℕ)
      (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F), Q n P →
        sysVal Xo c nab y k F P = sysVal Xo c nab' y k F P

theorem UniqueOn.mono {Q Q' : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop} (h : UniqueOn Xo c Q)
    (hQ : ∀ n P, Q' n P → Q n P) : UniqueOn Xo c Q' :=
  fun nab nab' h1 h2 S _ _ y k n F P hP => h nab nab' h1 h2 S y k n F P (hQ n P hP)

theorem uniqueOn_span_iff (Q : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop) :
    (UniqueOn Xo c fun n P => P ∈ Submodule.span c.F {P' | Q n P'}) ↔ UniqueOn Xo c Q := by
  refine ⟨fun h => h.mono Xo c fun n P hP => Submodule.subset_span hP, ?_⟩
  intro h _ nab nab' h1 h2 S _ _ y k n F P hP
  unfold sysVal
  rw [← colSumL_apply, ← colSumL_apply]
  refine LinearMap.eqOn_span ?_ hP
  intro P' hP'
  rw [colSumL_apply, colSumL_apply]
  exact h nab nab' h1 h2 S y k n F P' hP'

theorem span_harmA_eq (n : ℕ) :
    Submodule.span c.F {P : MvPolynomial (LtN Dw n) c.F | ∃ a, P ∈ harmA c a n} =
      Submodule.span c.F {P | IsTopHarmonic c P} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro P ⟨a, ha⟩
    rw [mem_harmA_iff] at ha
    exact ⟨ha.1, ha.2.1, a, ha.2.2.1⟩
  · refine Submodule.span_le.2 ?_
    rintro P ⟨h1, h2, a, h3⟩
    obtain ⟨N, hN, hP, -⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P
      ⟨(isHarmonic_iff_cmType c P).1 h1, h2, h3⟩
    have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have := Submodule.smul_mem _ (N : c.F)⁻¹ (Submodule.subset_span
      (s := {P : MvPolynomial (LtN Dw n) c.F | ∃ a, P ∈ harmA c a n}) ⟨a, hP⟩)
    rwa [inv_smul_smul₀ hN'] at this

theorem thExprUniqSt_iff_harmA : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), UniqueOn Xo c fun n P => ∃ a, P ∈ harmA c a n := by
  constructor
  · rintro h E _ _ _ H Dw l Xo c _ nab nab' h1 h2 S _ _ y k n F P ⟨a, ha⟩
    letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
    exact h E H Dw l Xo c nab nab' h1 h2 S y k n F a P ha
  · intro h E _ _ _ H Dw l Xo c _ nab nab' h1 h2 S _ _ _ y k n F a P ha
    exact h E H Dw l Xo c nab nab' h1 h2 S y k n F P ⟨a, ha⟩

theorem thExprUniqSt_iff_span : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l),
      UniqueOn Xo c fun n P => P ∈ Submodule.span c.F {P' : MvPolynomial (LtN Dw n) c.F | IsTopHarmonic c P'} := by
  rw [thExprUniqSt_iff_harmA]
  refine forall₅_congr fun E _ _ _ H => forall₄_congr fun Dw l Xo c => ?_
  rw [← uniqueOn_span_iff]
  simp only [span_harmA_eq]

theorem thExprUniqSt_iff_top : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), UniqueOn Xo c fun _ P => IsTopHarmonic c P := by
  rw [thExprUniqSt_iff_span]
  exact forall₅_congr fun E _ _ _ H => forall₄_congr fun Dw l Xo c => uniqueOn_span_iff Xo c _

section Reframe




end Reframe

end GlobalTheory.NabUniqCompare
end
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem nabVal_character_columns_of_canonGauge : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) :=
  GlobalTheory.nabVal_character_columns (GlobalTheory.exists_integral_germ_nabVal_congr
    GlobalTheory.canonGauge_dmonOf_hL_natCast_mul GlobalTheory.dmonOf_mul_congr_of_congr)

end GlobalTheory
end
