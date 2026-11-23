module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
public import Mathlib.RingTheory.FormalGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrder
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecomposition
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle053
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle064
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle092
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle019
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
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → ∀ τ : E →+* ℂ, IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) ∧ Function.Surjective (res (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j))) := by
  first | exact @GlobalTheory.CharDepth.isEigBasis_valExt | exact GlobalTheory.CharDepth.isEigBasis_valExt | (intros; apply GlobalTheory.CharDepth.isEigBasis_valExt <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst : ∀ (q : ℕ) [Fact q.Prime], (∀ (ζ ξ : ℂ_[q]) (f : ℂ_[q]⟦X⟧), ‖ζ - 1‖ < 1 → ‖ξ - 1‖ < 1 → Bdd f → shiftS ζ (shiftS ξ f) = shiftS (ζ * ξ) f) ∧ ∀ (ζ : ℂ_[q]) (n k : ℕ) (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧), ζ ^ (q ^ n) = 1 → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → Bdd f → ‖ζ - 1‖ < 1 ∧ shiftS ζ (f.subst (mulS a : ℂ_[q]⟦X⟧)) = (shiftS (ζ ^ k) f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  first | exact @GlobalTheory.MomOne.ShiftComp.main | exact GlobalTheory.MomOne.ShiftComp.main | (intros; apply GlobalTheory.MomOne.ShiftComp.main <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder : ∀ (q : ℕ) [Fact q.Prime] (F : FormalGroup 𝓞_ℂ_[q]) (U ℓ : ℂ_[q]⟦X⟧), constantCoeff U = 0 → constantCoeff ℓ = 0 → U.subst ℓ = X → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U → (∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ))) ∧ (∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1) ∧ (‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1 → ∀ (k : ℕ) (a : ℤ_[q]), ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) → ∀ n < (2 * q) ^ k, ‖coeff n (U.subst (C (zc a) * ℓ))‖ < 1) := by
  first | exact @GlobalTheory.MomOne.FormalMul.padic_multiplications | exact GlobalTheory.MomOne.FormalMul.padic_multiplications | (intros; apply GlobalTheory.MomOne.FormalMul.padic_multiplications <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
namespace CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → E) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → E) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [Formalism.REAL.RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem sum_mem {ι : Type} (A : ℝ) (f : ι → B.Mat k r → E) (t : Finset ι)
    (hf : ∀ i ∈ t, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC A m (f i)) :
    B.CkOn ⊤ (B.GV k r) (∑ i ∈ t, f i) ∧ ∀ m : ℕ, B.InCC A m (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine ⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
      fun m => ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩⟩
    intro u v _ _ _ g _
    simp [dLR_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := hf i (Finset.mem_insert_self _ _)
    obtain ⟨h3, h4⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨Formalism.FourierDecayAlt.P.B4.ckOn_add h1 h3, fun m => ?_⟩
    obtain ⟨c, hc⟩ := h2 m
    obtain ⟨c', hc'⟩ := h4 m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r E A m _ _ c c' 1 hc hc').1⟩

end CoefDecay

namespace CoefDecay

private theorem pair_bound (H : Hyps) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) (hR : R.IsDS ε mu) (hgap : Formalism.QuantumDeterminants.GapAtLeast ε mu h) (hok : GapOK k r h)
    (x y : R.H) (hx : x ∈ R.TK) (hy : y ∈ R.TK) :
    ∃ c : ℝ, ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪x, R.σ g y⟫_ℂ‖ ≤ c := by
  obtain ⟨C, Ws, -, hb⟩ := GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok x hx
  have hys : y ∈ R.sm := (GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hR).2.2.2.2.1 y hy
  refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W y‖).sum, fun g hg => ?_⟩
  have pg := GlobalTheory.BesselDecay.gN_pos' hg
  have h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1 := by
    rw [← Real.rpow_add pg]; simp
  have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos pg _
  refine (mul_le_mul_of_nonneg_left (hb y hys g hg) pg'.le).trans (le_of_eq ?_)
  rw [mul_left_comm, h3, mul_one]

private theorem coef_bound : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ m : ℕ, ∃ c : ℝ, ∀ a b : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → (∀ Y ∈ b, B.unitLie k r Y) → a.length + b.length ≤ m → ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ‖ ≤ c := by
  intro H k r ε mu h R hR hgap hok x hx y hy m
  obtain ⟨M, xs, hxs, hxa⟩ := GlobalTheory.UnitBoxWords.box_words H.1.2.2.1 k r ε mu R hR x hx m
  obtain ⟨N, ys, hys, hyb⟩ := GlobalTheory.UnitBoxWords.box_words H.1.2.2.1 k r ε mu R hR y hy m
  choose c hc using fun (i : Fin M) (j : Fin N) => pair_bound H R hR hgap hok (xs i) (ys j) (hxs i) (hys j)
  refine ⟨∑ i, ∑ j, c i j, fun a b ha hb hl g hg => ?_⟩
  obtain ⟨co, hco, ea⟩ := hxa a ha (by omega)
  obtain ⟨co', hco', eb⟩ := hyb b hb (by omega)
  have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos (GlobalTheory.BesselDecay.gN_pos' hg) _

  rw [ea, eb, map_sum, sum_inner]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_sum]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => le_trans (mul_le_mul_of_nonneg_left ?_ pg'.le) (hc i j g hg)
  rw [map_smul, inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have n0 := norm_nonneg ⟪xs i, R.σ g (ys j)⟫_ℂ
  calc _ ≤ 1 * (1 * ‖⟪xs i, R.σ g (ys j)⟫_ℂ‖) := by
        gcongr
        · exact hco i
        · exact hco' j
    _ = _ := by ring

end CoefDecay

theorem isCoef_ckOn_inCC : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ l l' F s hR hg hok hF
  obtain ⟨n, x, y, X, hxy, hFe, -⟩ := hF
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  let f : Fin n → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m (f i) := by
    intro i _
    obtain ⟨h1, h2⟩ := GlobalTheory.CoeffDeriv.coeff_dLR hK k r ε mu R (Wq →L[ℂ] Wp) (X i) (f i) hR (x i) (hsm _ (hxy i).1)
      (y i) (hsm _ (hxy i).2) (fun g _ => rfl)
    refine ⟨h1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := CoefDecay.coef_bound hH k r ε mu h R hR hg hok (x i) (hxy i).1 (y i) (hxy i).2 m
    refine ⟨c * ‖X i‖, Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top h1, fun u v hu hv hlen g hgG => ?_⟩
    rw [h2 u v (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) g hgG, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc u v hu hv hlen g hgG) (norm_nonneg _)
  obtain ⟨h1, h2⟩ := CoefDecay.sum_mem (aOf r h - 1) f Finset.univ hf
  have hc := GlobalTheory.ckOn_inCC_congr_on_group k r (Wq →L[ℂ] Wp) (aOf r h - 1) (∑ i, f i) F
    (fun g hgG => by rw [hFe g hgG, Finset.sum_apply])
  exact ⟨hc.1 h1, fun m => hc.2 m (h2 m)⟩

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPhi

theorem hsInner_smul_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (a b : ℂ) (A A' : Wq →L[ℂ] Wp) :
    B.hsInner (a • A) (b • A') = a * star b * B.hsInner A A' := by
  have h : ∀ (c : ℂ) (Y : Wq →L[ℂ] Wp), B.hsVec (c • Y) = c • B.hsVec Y := fun c Y => rfl
  unfold B.hsInner
  rw [h, h, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  ring

theorem isUnit_det_of_mem {k r : ℕ} {g : Mx k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have h : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h1 : (Formalism.QuantumDeterminants.Hpk k r * (gᴴ * Formalism.QuantumDeterminants.Hpk k r)) * g = 1 := by
    rw [Matrix.mul_assoc, h]; exact PI.HwUniqW.Hpk_mul_self
  exact Matrix.isUnit_det_of_left_inverse h1

theorem haar_left {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem Ph_coeff : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDS ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  intro hH k r ε mu R Wp _ _ _ _ Wq _ _ _ _ D dd hR hdd x y x' y' X X' p hp
  obtain ⟨hmul, hone, hinner, -, -, -, -, ⟨w, hw, -⟩, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hR
  obtain ⟨c, -, hc⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r ε D.μG (haar_left D.haarG)
  obtain ⟨hdeg, hS⟩ := hc mu R hR
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hd : c * Formalism.QuantumDeterminants.fdegHC mu = dd := (hdeg w hw0).symm.trans (hdd w hw0)
  obtain ⟨hI, hE⟩ := hS (R.σ (JF.sR p) y) (R.σ (JF.sL p) x) y' x'
  rw [hd] at hE
  have ha : (Matrix.of p.1.1 : Mx k r) ∈ GG k r := hp.1.1
  have hb : (Matrix.of p.1.2 : Mx k r) ∈ GG k r := hp.2.1.1
  have hc' : (Matrix.of p.2.1 : Mx k r) ∈ GG k r := hp.2.2.1.1
  have hd' : (Matrix.of p.2.2 : Mx k r) ∈ GG k r := hp.2.2.2.1
  have hL : JF.sL p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hb ha
  have hRR : JF.sR p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd' hc'
  have hLi : (JF.sL p)⁻¹ ∈ GG k r := PI.HwUniqW.inv_mem_UH hL
  set Y := (D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹)) with hY
  have key : ∀ g ∈ GG k r, B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) g) (⟪x', R.σ g y'⟫_ℂ • X') =
      ⟪R.σ (JF.sL p) x, R.σ g (R.σ (JF.sR p) y)⟫_ℂ * star ⟪x', R.σ g y'⟫_ℂ * B.hsInner Y X' := by
    intro g hg
    have e1 : B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) g = ⟪x, R.σ (B.sgs p g) y⟫_ℂ • Y := by
      unfold B.rho
      rw [hY, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    have e2 : B.sgs p g = (JF.sL p)⁻¹ * (g * JF.sR p) := by
      unfold B.sgs JF.sL JF.sR
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    have hgR : g * JF.sR p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg hRR
    have e3 : ⟪x, R.σ (B.sgs p g) y⟫_ℂ = ⟪R.σ (JF.sL p) x, R.σ g (R.σ (JF.sR p) y)⟫_ℂ := by
      rw [← hinner _ hL, e2, ← hmul _ hL _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hLi hgR), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_mem hL), Matrix.one_mul, hmul _ hg _ hRR]
    rw [e1, e3, hsInner_smul_smul]
  have hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mx k r) ∈ GG k r := by
    rw [ae_iff]; exact D.haarG.conc
  have hae2 : (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g))
      (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) =ᵐ[D.μG] fun g => ⟪R.σ (JF.sL p) x, R.σ (Matrix.of g) (R.σ (JF.sR p) y)⟫_ℂ *
        star ⟪x', R.σ (Matrix.of g) y'⟫_ℂ * B.hsInner Y X' := hae.mono fun g hg => key _ hg
  refine ⟨(hI.mul_const _).congr hae2.symm, ?_⟩
  unfold B.Ph
  rw [integral_congr_ae hae2, integral_mul_const, hE]

end GlobalTheory.BesselPhi
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliSmooth

lemma entry_conj {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * P') c d = P c a * P' b d := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, mul_zero]
  · simp

theorem qdet_smooth : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  intro hyp k r ε mu R hR Q E hQ hE Y w
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hC := hyp.2.2.1
  obtain ⟨hmu, Q0, hQ0, hDS⟩ := id hR
  have hU0 : IsUnit Q0 := hQ0.1.1
  obtain ⟨E0, hE0, hgl⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0
  obtain ⟨hsm, hd⟩ := GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport k r ε R Q0 hQ0
  obtain ⟨-, hexp, -⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0
  have hdQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hdQ0 : IsUnit Q0.det := (Matrix.isUnit_iff_isUnit_det Q0).1 hU0
  have hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹) := by
    funext a b
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hE a b v, hexp]
    have h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ =
        (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]
  have h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]
  rw [hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]
  apply Subtype.ext
  have h4 := GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0
    (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w
  rw [← h4, hC _ ε mu R.H _ hmu hDS w (hsm w w.2) Y]
  rfl

end GlobalTheory.CapelliSmooth
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.pieri_tensor_decomposition : Hyps → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → ∀ ν, (∀ l, n1 ν + l ≤ q0 → ∃ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep) ∧ (n1 ν + 1 ≤ q0 → ∃ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep) := by
  first | exact @GlobalTheory.TensExists.tens_exists | exact GlobalTheory.TensExists.tens_exists | (intros; apply GlobalTheory.TensExists.tens_exists <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CayleyTens

theorem gram_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    PI.UpqRep.Hpk k r j i = Formalism.QuantumDeterminants.Hpk k r i j := by
  unfold PI.UpqRep.Hpk Formalism.QuantumDeterminants.Hpk
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [hij, hji, and_false, if_false]
    split_ifs <;> first | rfl | omega

theorem gram_cayley {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Q : Mx k r}
    (hQ : PI.UpqRep.IsCayleyU k r ε Q) (i j : Fin (2 * r + k + 1)) :
    ∑ d, (if ε d then (1 : ℂ) else -1) * ((starRingEnd ℂ) (Q⁻¹ i d) * Q⁻¹ j d) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv (by
    have := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    simpa [Matrix.star_eq_conjTranspose] using this)
  rw [← gram_symm, ← hQ.1.2, hinv, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [PI.UpqRep.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  by_cases h : ε d <;> simp [h, mul_comm]

theorem hhJ_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Q : Mx k r}
    (hQ : PI.UpqRep.IsCayleyU k r ε Q) (R : Rep k r) (x y : Fin (2 * r + k + 1) → R.smSub)
    (u v : Fin (2 * r + k + 1) → R.H)
    (hx : ∀ d, ((x d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • u c)
    (hy : ∀ d, ((y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • v c) :
    hhJ ε x y = hh (Formalism.QuantumDeterminants.Hpk k r) R u v := by
  unfold hhJ hh
  simp only [← gram_cayley hQ, Submodule.coe_inner, hx, hy, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem algTens_cayley : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (ep : Fin (2 * r + k + 1) → ℝ) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensH dualM (Formalism.QuantumDeterminants.Hpk k r) R RI io pr ep → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), AlgTens ε E (fun s => (RI s).smSub) F io' pr' ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  intro hK k r ε mu R hR RI muI io pr ep Q E F hRI hT hQ hE hF
  obtain ⟨io', pr', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.T.dual_tensor_cayley_compatible hK k r ε mu R hR RI muI io pr Q E F hRI hT.raw hQ.1.1 hE hF
  refine ⟨io', pr', ⟨h1, h2, h3, h4, h5, ?_, ?_⟩, h7⟩
  · intro s t hst y y'
    rw [hhJ_eq hQ R _ _ _ _ (h6 s y) (h6 t y')]
    exact hT.orth s t hst _ y.2 _ y'.2
  · intro s
    refine ⟨ep s, hT.ep_sq s, fun y y' => ?_⟩
    rw [hhJ_eq hQ R _ _ _ _ (h6 s y) (h6 s y'), Submodule.coe_inner]
    exact hT.iso s _ y.2 _ y'.2

end GlobalTheory.CayleyTens
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem eLpNorm_two_of_lintegral_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) (c : ℝ) (hc : 0 ≤ c) (hf : AEStronglyMeasurable f μ) (h : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (c ^ 2)) :
    eLpNorm f 2 μ = ENNReal.ofReal c := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf]
  have h2 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ = ENNReal.ofReal c ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.rpow_two, ← h]
    refine lintegral_congr fun x => ?_
    simp [enorm_eq_nnnorm]
  rw [h2, ← ENNReal.rpow_mul]
  norm_num

theorem integral_inner_of_isometric {α E F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (S : Submodule ℂ E) (Φ : E → α → F)
    (hm : ∀ w ∈ S, MemLp (Φ w) 2 μ) (hn : ∀ w ∈ S, eLpNorm (Φ w) 2 μ = ENNReal.ofReal ‖w‖)
    (hadd : ∀ v ∈ S, ∀ w ∈ S, Φ (v + w) =ᵐ[μ] Φ v + Φ w)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ S, Φ (c • v) =ᵐ[μ] c • Φ v) :
    ∀ w ∈ S, ∀ w' ∈ S, ∫ x, ⟪Φ w' x, Φ w x⟫_ℂ ∂μ = ⟪w', w⟫_ℂ := by
  let L : S →ₗᵢ[ℂ] Lp F 2 μ :=
    { toFun := fun v => (hm v v.2).toLp (Φ v)
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hadd v v.2 w w.2)
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hsmul c v v.2)
      norm_map' := fun v => by
        change ‖(hm v v.2).toLp (Φ v)‖ = _
        rw [Lp.norm_toLp, hn v v.2, ENNReal.toReal_ofReal (norm_nonneg _)]
        rfl }
  intro w hw w' hw'
  have h := L.inner_map_map ⟨w', hw'⟩ ⟨w, hw⟩
  rw [L2.inner_def] at h
  refine Eq.trans ?_ h
  refine integral_congr_ae ?_
  filter_upwards [(hm w hw).coeFn_toLp, (hm w' hw').coeFn_toLp] with x h1 h2
  change _ = ⟪((hm w' hw').toLp (Φ w')) x, ((hm w hw).toLp (Φ w)) x⟫_ℂ
  rw [h1, h2]

theorem isoBessel_polarised : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq) ∧ ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∫ x, ⟪Bm (R.σ (Matrix.of x) w'), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = ⟪w', w⟫_ℂ := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq Bm hDS hS hB
  obtain ⟨hae, -, -, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hDS hS
  obtain ⟨-, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hDS
  have hn : ∀ w ∈ R.sm, eLpNorm (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq =
      ENNReal.ofReal ‖w‖ := fun w hw =>
    eLpNorm_two_of_lintegral_sq _ _ (norm_nonneg _) (hmeas Bm hB.1 w hw) (hB.2 w hw)
  have hm : ∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq := fun w hw =>
    by rw [memLp_iff, hn w hw]; exact ENNReal.ofReal_lt_top
  refine ⟨hm, ?_⟩
  refine integral_inner_of_isometric R.smSub
    (fun w (x : Formalism.QuantumDeterminants.Mt k r) => Bm (R.σ (Matrix.of x) w)) hm hn ?_ ?_
  · intro v hv w hw
    filter_upwards [hae] with x hx
    simp only [Pi.add_apply, map_add (f := _)]
    exact hB.1.1 _ (hsm _ hx v hv) _ (hsm _ hx w hw)
  · intro c v hv
    filter_upwards [hae] with x hx
    simp only [Pi.smul_apply, map_smul]
    exact hB.1.2.1 c _ (hsm _ hx v hv)

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : Mx k r), γ ∈ GG k r → (∀ F F' : Mx k r → (Wq →L[ℂ] Wp), (∀ g ∈ GG k r, F g = F' g) → B.JF D F γ = B.JF D F' γ ∧ (Integrable (JF.integrand D F γ) D.μSS → Integrable (JF.integrand D F' γ) D.μSS)) ∧ (∀ (φ : Mx k r → ℂ) (F : Mx k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → φ (B.sgs p γ) = φ γ) → B.JF D (fun g => φ g • F g) γ = φ γ • B.JF D F γ) ∧ (∀ (ι : Type) [Fintype ι] (F : ι → Mx k r → (Wq →L[ℂ] Wp)), (∀ i, Integrable (JF.integrand D (F i) γ) D.μSS) → B.JF D (fun g => ∑ i, F i g) γ = ∑ i, B.JF D (F i) γ) ∧ ∀ᵐ p ∂D.μSS, D.inSS p := by
  first | exact @GlobalTheory.BesselFunctionBasic.JF_basic | exact GlobalTheory.BesselFunctionBasic.JF_basic | (intros; apply GlobalTheory.BesselFunctionBasic.JF_basic <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent : ∀ (k r : ℕ) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)), (PI.BesselPeriodGGP.IsHaarOn (GG k r) μ ↔ B.IsHaarOn (GG k r) μ) ∧ (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) ∧ ∀ z, Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → 1 ≤ k → (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ) := by
  first | exact @GlobalTheory.HaarNotions.isHaarOn_iff_groups | exact GlobalTheory.HaarNotions.isHaarOn_iff_groups | (intros; apply GlobalTheory.HaarNotions.isHaarOn_iff_groups <;> assumption)
end
