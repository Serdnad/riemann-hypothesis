module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle383
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle333
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle354
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac.DCoset

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem tor_inv (ϖ : kˣ) (x : Fin n → ℤ) : (tor ϖ x)⁻¹ = tor ϖ (fun i => - x i) := by
  unfold tor
  rw [← map_inv]
  congr 1
  funext i
  simp [_root_.zpow_neg]

theorem conj_apply (ϖ : kˣ) (x : Fin n → ℤ) (l : GL (Fin n) k) (i j : Fin n) :
    (((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j := by
  rw [tor_inv, Units.val_mul, Units.val_mul]
  unfold tor
  rw [val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, add_comm (x j),
    _root_.zpow_add, Units.val_mul]
  ring

theorem val_zpow_lt_one {ϖ : kˣ} (hϖ : ord k ϖ = 1) {m : ℤ} (hm : 0 < m) :
    valuation k ((ϖ ^ m : kˣ) : k) < 1 := by
  have h := GlobalTheory.OrdShellInt.val_le_iff_ord (k := k) 1 (ϖ ^ m)
  have h_one : ord k (1 : kˣ) = 0 := ord_eq_zero (k := k) (by simp)
  rw [GlobalTheory.OrdShellInt.ord_zpow, hϖ, h_one] at h
  rw [Units.val_one, map_one] at h
  exact not_le.1 fun h' => absurd (h.1 h') (by omega)

theorem conj_entries {ϖ : kˣ} (hϖ : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {l : GL (Fin n) k}
    (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) (i j : Fin n) :
    valuation k ((((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 ∧
      (j < i → valuation k ((((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) < 1) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hl.2
  have hint : valuation k ((l : Matrix (Fin n) (Fin n) k) i j) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff l).1 (iwahori_le_KO k (Fin n) hl.1)).1 i j)
  rw [conj_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [h0 i j h, mul_zero, map_zero]
    exact ⟨zero_le', fun h' => absurd h' h.not_gt⟩
  · rw [h1, sub_self]
    simp
  · have hlt : valuation k (((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j) < 1 := by
      rw [map_mul]
      refine lt_of_le_of_lt (mul_le_mul' le_rfl hint) ?_
      rw [mul_one]
      exact val_zpow_lt_one hϖ (sub_pos.2 (hx h))
    exact ⟨hlt.le, fun _ => hlt⟩

theorem conj_mem_iwahori {ϖ : kˣ} (hϖ : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {l : GL (Fin n) k}
    (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) :
    (tor ϖ x)⁻¹ * l * tor ϖ x ∈ iwahori k (Fin n) := by
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩,
    fun i j hij => (conj_entries hϖ hx hl i j).2 hij⟩
  · exact (Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx hl i j).1
  · have e : ((tor ϖ x)⁻¹ * l * tor ϖ x)⁻¹ = (tor ϖ x)⁻¹ * l⁻¹ * tor ϖ x := by group
    rw [e]
    exact (Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx (inv_mem hl) i j).1

theorem diagT_conj_tor (ϖ : kˣ) (x : Fin n → ℤ) (s : Fin n → kˣ) :
    tor ϖ x * diagT k (Fin n) s * (tor ϖ x)⁻¹ = diagT k (Fin n) s := by
  have e : tor ϖ x * diagT k (Fin n) s = diagT k (Fin n) s * tor ϖ x := by
    unfold tor
    rw [← map_mul, ← map_mul, mul_comm]
  rw [e]
  group

end GlobalTheory.CompanionTheory.IwJac.DCoset

namespace GlobalTheory.CompanionTheory.IwJac

end GlobalTheory.CompanionTheory.IwJac

end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.continuous_archimedean_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ), Ker ν β → Continuous f → Continuous (sm ν β f) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.continuous_sm_of_ker | exact GlobalTheory.CompanionTheory.Conc.continuous_sm_of_ker | (intros; apply GlobalTheory.CompanionTheory.Conc.continuous_sm_of_ker <;> assumption)
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.killed_by_polynomial_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ) (r : ℕ) (p : ℂ[X]), Ker ν β → 0 < r → r < n → Continuous f →
  An.Kill r f p → An.Kill r (sm ν β f) p := by
  first | exact @GlobalTheory.CompanionTheory.Conc.kill_sm | exact GlobalTheory.CompanionTheory.Conc.kill_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.kill_sm <;> assumption)
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.smoothing_lipschitz_bound : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ), Ker ν β → ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
  ∀ (f : AdelicGLn.AdelicGL K n → ℂ), Continuous f → ∀ g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖f (g * q)‖ ≤ M) →
    ‖sm ν β f (g * CuspidalSpectrum.archExp Y) - sm ν β f g‖ ≤ C * ‖Y‖ * M := by
  first | exact @GlobalTheory.CompanionTheory.Conc.sm_lip_of_sq_zero | exact GlobalTheory.CompanionTheory.Conc.sm_lip_of_sq_zero | (intros; apply GlobalTheory.CompanionTheory.Conc.sm_lip_of_sq_zero <;> assumption)
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.uniform_bound_of_archimedean_lipschitz : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) (f₀ f₁ : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ), 0 < r → r < n → UFam f₁ →
  (∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧ ∀ i g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R →
    (∀ q ∈ Q₀, ‖f₀ i (g * q)‖ ≤ M) → ‖f₁ i (g * CuspidalSpectrum.archExp Y) - f₁ i g‖ ≤ C * ‖Y‖ * M) →
  UBnd f₀ m → UBnd (fun i g => f₁ i g - An.ctn r (f₁ i) g) (Function.update m r (m r - 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.diffStepU | exact GlobalTheory.CompanionTheory.Conc.diffStepU | (intros; apply GlobalTheory.CompanionTheory.Conc.diffStepU <;> assumption)
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.uniform_bound_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ), Ker ν β → (∀ i, Continuous (f i)) →
  UBnd f m → UBnd (fun i => sm ν β (f i)) m := by
  first | exact @GlobalTheory.CompanionTheory.Conc.uBnd_sm | exact GlobalTheory.CompanionTheory.Conc.uBnd_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.uBnd_sm <;> assumption)
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.uniform_family_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ), Ker ν β → UFam f → UFam (fun i => sm ν β (f i)) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.uFam_sm | exact GlobalTheory.CompanionTheory.Conc.uFam_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.uFam_sm <;> assumption)
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.ConjEv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_box_iff_forall_valuation_le {m : ℕ} {s : kˣ} {x : Fin m → k} :
    x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s ↔ ∀ j, valuation k (x j) ≤ valuation k (s : k) :=
  Iff.rfl

theorem exists_mulVec_box (m : ℕ) (g : Matrix (Fin m) (Fin m) k) (t : kˣ) :
    ∃ t' : kˣ, ∀ x ∈ box m t, g *ᵥ x ∈ box m t' := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · exact ⟨t, fun x _ => mem_box_iff_forall_valuation_le.2 fun j => isEmptyElim j⟩
  obtain ⟨ij, hij⟩ := Finite.exists_max (fun ij : Fin m × Fin m => valuation k (g ij.1 ij.2))
  by_cases h0 : g ij.1 ij.2 = 0
  · refine ⟨t, fun x _ => ?_⟩
    have hg : g = 0 := by
      ext i j
      simpa [h0] using hij (i, j)
    rw [hg, Matrix.zero_mulVec]
    exact zero_mem _
  · refine ⟨Units.mk0 _ h0 * t, fun x hx => ?_⟩
    rw [mem_box_iff_forall_valuation_le] at hx ⊢
    intro i
    show valuation k (∑ j, g i j * x j) ≤ _
    refine Finset.sum_induction _ (fun y => valuation k y ≤ valuation k ((Units.mk0 _ h0 * t : kˣ) : k))
      (fun a b ha hb => (valuation k).map_add_le ha hb) (by simp) (fun j _ => ?_)
    rw [map_mul, Units.val_mul, map_mul, Units.val_mk0]
    exact mul_le_mul' (hij (i, j)) (hx j)

theorem box_mono {m : ℕ} {t t' : kˣ} (h : valuation k (t : k) ≤ valuation k (t' : k)) :
    ∀ x ∈ box m t, x ∈ box m t' := by
  intro x hx
  rw [mem_box_iff_forall_valuation_le] at hx ⊢
  exact fun j => le_trans (hx j) h


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem val_mul_inv_le {c r t : kˣ} (h : valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t : k)) :
    valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  have e1 : c * t⁻¹ = (c * r⁻¹) * (r * t⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left]
  have e2 : t * (r * t⁻¹) = r := by
    rw [mul_comm r, ← mul_assoc, mul_inv_cancel, one_mul]
  calc valuation k ((c * t⁻¹ : kˣ) : k)
      = valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((r * t⁻¹ : kˣ) : k) := by
        rw [e1, Units.val_mul, map_mul]
    _ ≤ valuation k (t : k) * valuation k ((r * t⁻¹ : kˣ) : k) := mul_le_mul' h le_rfl
    _ = valuation k (r : k) := by
        rw [← map_mul, ← Units.val_mul, e2]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem wt_mir (ψ : AddChar k Circle) {n : ℕ} (p : Mir k n) (y : Fin (n + 1) → k) :
    wt ψ n (((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) = wt ψ n y := by
  unfold GlobalTheory.CompanionTheory.MirPair.wt
  rw [GlobalTheory.BZMir.mulVec_last_of_mem k _ p.2]

theorem absPow_succ_val (s : ℕ) (u : kˣ) :
    ((absPow k ((s + 1 : ℕ) : ℂ) u : ℂˣ) : ℂ) = ((absPow k (s : ℂ) u : ℂˣ) : ℂ) * ((nabs k u : ℝ) : ℂ) := by
  rw [show ((s + 1 : ℕ) : ℂ) = (s : ℂ) + 1 by push_cast; ring, GlobalTheory.SmGL.absPow_add,
    MonoidHom.mul_apply, Units.val_mul, GlobalTheory.SmGL.val_absPow k 1, Complex.cpow_one]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
  (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ)

theorem JJ_conj (hB : TwInv T T' B s) (p : Mir k n) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') :
    JJ ν ψ T B M (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
        (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') =
      ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
        JJ ν ψ T B {y | ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} v v' := by
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hw : ∀ x : Fin (n + 1) → k, GlobalTheory.CompanionTheory.MirPair.wt ψ n x =
      GlobalTheory.CompanionTheory.MirPair.wt ψ n
        ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := GlobalTheory.CompanionTheory.MirPair.ConjEv.wt_mir ψ p⁻¹ x
    rw [Subgroup.coe_inv] at h
    exact h.symm
  have hF := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (p : GL (Fin (n + 1)) k) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n y * GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  have key : ∀ x : Fin (n + 1) → k,
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x *
                   GlobalTheory.CompanionTheory.MirPair.coef T B (T (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
                     (T' (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') x =
        ((GlobalTheory.SmGL.detChar (Fin (n + 1)) (GlobalTheory.SmGL.absPow k (s : ℂ))
            (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
          (GlobalTheory.CompanionTheory.MirPair.wt ψ n
                       ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) *
            GlobalTheory.CompanionTheory.MirPair.coef T B v v'
              ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
    intro x
    rw [hlevi, ← hw]
    ring
  unfold GlobalTheory.CompanionTheory.MirPair.JJ
  simp only [key]
  rw [integral_const_mul, hF, ← mul_assoc]
  congr 1
  rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.ConjEv.absPow_succ_val]

end GlobalTheory.CompanionTheory.MirPair.ConjEv

namespace GlobalTheory.CompanionTheory.MirPair

theorem evVal_conj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (p : Mir k n) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') (((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB p v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨r, hr⟩ := GlobalTheory.T.mirabolic_pairing_conductor_bound ν ψ c T T' B s hψ hc hT hT' hB
    (p : GL (Fin (n + 1)) k) v v'
  obtain ⟨t₁, ht₁₀, ht₁r⟩ : ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t₁ : k) := by
    rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
    · exact ⟨c * r⁻¹, h, le_rfl⟩
    · exact ⟨t₀, le_rfl, h⟩
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.CompanionTheory.MirPair.ConjEv.exists_mulVec_box (n + 1)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) t₁
  refine ⟨t₂, fun t ht => ?_⟩
  rw [GlobalTheory.CompanionTheory.MirPair.ConjEv.JJ_conj ν ψ T T' B s hB p]
  congr 1
  rw [← ht₀ t₁ ht₁₀]
  exact hr t₁ (GlobalTheory.CompanionTheory.MirPair.ConjEv.val_mul_inv_le ht₁r) t
    (fun x hx => GlobalTheory.CompanionTheory.MirPair.ConjEv.box_mono ht _ (ht₂ x hx))

end GlobalTheory.CompanionTheory.MirPair

end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem exists_evVal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (v : V) (v' : V'), ∃ A, EvVal ν ψ T B v v' A := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB v v'
  obtain ⟨r, hr⟩ := GlobalTheory.T.mirabolic_pairing_conductor_bound ν ψ c T T' B s hψ hc hT hT' hB 1 v v'
  refine ⟨JJ ν ψ T B (box (n + 1) (c * r⁻¹) : Set (Fin (n + 1) → k)) v v', c * r⁻¹, fun t ht => ?_⟩
  have hc' : valuation k ((c * (c * r⁻¹)⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
    have : c * (c * r⁻¹)⁻¹ = r := by
      rw [_root_.mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
    rw [this]
  have hsub : ∀ x ∈ box (n + 1) (c * r⁻¹), ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t := by
    intro x hx
    rw [Units.val_one, one_mulVec]
    rw [BZOnto.PerpSmall.mem_box] at hx ⊢
    exact fun i => show valuation k (x i) ≤ valuation k (t : k) from
      le_trans (show valuation k (x i) ≤ valuation k ((c * r⁻¹ : kˣ) : k) from hx i) ht
  have h := hr (c * r⁻¹) hc' t hsub
  rw [← h]
  simp only [Units.val_one, one_mulVec]
  rfl

end GlobalTheory.CompanionTheory.MirPair
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibUnip

theorem map_smInt_translate {X Z Z' : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [MeasurableSpace X] [BorelSpace X] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z']
    (μ : MeasureTheory.Measure X) [μ.IsAddHaarMeasure]
    (L : Z →ₗ[ℂ] Z') (T : Z →ₗ[ℂ] Z) (hT : ∀ z, L (T z) = L z) (φ : X → Z) (m : X)
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    L (smInt μ (fun v => T (φ (v + m)))) = L (smInt μ φ) := by
  obtain ⟨_, h2, h3, _⟩ := SmIntEl.smInt_properties (X := X) (W := Z) (W' := Z) μ
  have hl' : IsLocallyConstant (φ ∘ fun v => v + m) := hl.comp_continuous ((continuous_id.add continuous_const))
  have hc' : HasCompactSupport (φ ∘ fun v => v + m) :=
    hc.comp_homeomorph (Homeomorph.addRight m)
  have e1 : smInt μ (T ∘ (φ ∘ fun v => v + m)) = T (smInt μ (φ ∘ fun v => v + m)) := h2 T _ hl' hc'
  have e2 : smInt μ (φ ∘ fun v => v + m) = smInt μ φ :=
    h3 (fun v => v + m) φ (MeasureTheory.measurePreserving_add_right μ m) hl
  calc L (smInt μ (fun v => T (φ (v + m)))) = L (T (smInt μ (φ ∘ fun v => v + m))) :=
        congrArg L e1
    _ = L (smInt μ (φ ∘ fun v => v + m)) := hT _
    _ = L (smInt μ φ) := congrArg L e2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem midV_add (i t : ℕ) (v m : Fin t → k) :
    midV k i t (v + m) = midV k i t v + midV k i t m := by
  funext j
  induction j using Fin.addCases <;> simp [midV]

theorem mul_uM_eq (i t : ℕ) (g : GL (Fin (i + t)) k) (y : Fin (i + t) → k) (x : Fin i → k) (m v : Fin t → k)
    (hy : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    uM k (i + t) (midV k i t v) * levi k (i + t) g * uM k (i + t) y =
      uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g) := by
  have e : midV k i t v + (topV k i t x + midV k i t m) = topV k i t x + midV k i t (v + m) := by
    rw [midV_add]; abel
  rw [mul_assoc, levi_mul_uM, hy, ← mul_assoc, ← uM_add, e, uM_add, mul_assoc]

variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem clT_extTensor (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin i → k) (z : V ⊗[ℂ] W) :
    clT τ W (extTensor τ σ (uM k i x, 1) z) = clT τ W z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b =>
    have hq : (twKer τ (MirUin k i) 1).mkQ (τ (uM k i x) a) = (twKer τ (MirUin k i) 1).mkQ a := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨_, uM_mem k i x⟩, a, ?_⟩)
      simp
    rw [extTensor_tmul]
    simp only [clT, LinearMap.rTensor_tmul, map_one, Module.End.one_apply]
    exact congrArg (· ⊗ₜ[ℂ] b) hq



theorem fibV_prodPG (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (y : Fin (i + t) → k)
    (x : Fin i → k) (m v : Fin t → k)
    (hy : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    fibV (prodPG τ σ (uM k (i + t) y) f) g v = extTensor τ σ (uM k i x, 1) (fibV f g (v + m)) := by
  refine Exists.elim (GlobalTheory.T.unipotent_top_mem_parabolic k i t x) fun hmem hproj => ?_
  have e1 : fibV (prodPG τ σ (uM k (i + t) y) f) g v =
      f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g * uM k (i + t) y) := rfl
  have e2 := f.1.1.2 ⟨_, hmem⟩ (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g)
  calc fibV (prodPG τ σ (uM k (i + t) y) f) g v
      = f.1.1.1 (uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g)) :=
        e1.trans (congrArg f.1.1.1 (mul_uM_eq i t g y x m v hy))
    _ = extTensor τ σ (pgProj k i t ⟨_, hmem⟩) (fibV f g (v + m)) := e2
    _ = extTensor τ σ (uM k i x, 1) (fibV f g (v + m)) :=
        congrArg (fun a => extTensor τ σ a (fibV f g (v + m))) hproj

theorem fibInt_col (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (x : Fin i → k) (m : Fin t → k)
    (hxm : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    fibInt μ (prodPG τ σ (uM k (i + t) y) f) g = fibInt μ f g := by
  have hlc := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hfun : fibV (prodPG τ σ (uM k (i + t) y) f) g =
      fun v => (extTensor τ σ (uM k i x, 1)) (fibV f g (v + m)) :=
    funext fun v => fibV_prodPG τ σ f g y x m v hxm
  have h1 : clT τ W (smInt μ (fibV (prodPG τ σ (uM k (i + t) y) f) g)) =
      clT τ W (smInt μ fun v => (extTensor τ σ (uM k i x, 1)) (fibV f g (v + m))) :=
    congrArg (fun φ => clT τ W (smInt μ φ)) hfun
  exact h1.trans (map_smInt_translate μ (clT τ W) (extTensor τ σ (uM k i x, 1))
          (clT_extTensor τ σ x) (fibV f g) m hlc.1 hlc.2)



theorem fibInt_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (u : Mir k (i + t)), u ∈ MirUin k (i + t) → ∀ g : GL (Fin (i + t)) k, fibInt μ (prodPG τ σ u f) g = fibInt μ f g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f u hu g
  refine Exists.elim (exists_uM_of_mem k (i + t) hu) fun y hy => ?_
  refine Exists.elim (exists_top_mid k i t ((g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)) fun x hx => ?_
  refine Exists.elim hx fun m hxm => ?_
  exact (congrArg (fun u' => fibInt μ (prodPG τ σ u' f) g) hy).trans
    (fibInt_col τ σ hτ hσ μ f y g x m hxm)

end GlobalTheory.CompanionTheory.BZPsiPG.FibUnip

end
end
