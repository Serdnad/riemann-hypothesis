module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle004
public import GroundTheory.AutomorphicForms.ReductionCore
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SphericalFunctionIntegral

open Formalism.UG GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem le_one (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem mem_Ov (w : Pl E) {x : w.adicCompletion E} (h : x ∈ (ValuativeRel.valuation (w.adicCompletion E)).integer) :
    x ∈ Ov E w :=
  (le_one w x).1 ((Valuation.mem_integer_iff _ _).1 h)

theorem int_KGL (w : Pl E) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : x ∈ KGL w (n := k) := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 hx
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, mem_Ov w (h1 i j)⟩, Matrix.of fun i j => ⟨(x⁻¹ : GL (Fin k) (w.adicCompletion E)).1 i j, mem_Ov w (h2 i j)⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem fix {w : Pl E} {B : Multiset ℂˣ} {φ : XB E k} (h : SatFn w B φ) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : Rt E k (fl k w x) φ = φ := by
  rcases h with rfl | h
  · exact map_zero _
  · exact GlobalTheory.LGrp.mem_fixed.1 h.2.1 x (int_KGL w hx)

variable [_root_.NumberField.IsTotallyComplex E]

theorem step (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k) (g κ : GA E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ)
    (hinf : cInf κ = 1) (hS : ∀ w ∈ S, cLoc w κ = 1)
    (hint : ∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) (T : Finset (Pl E)) :
    ∃ h : GA E k, φ (g * h) = φ g ∧ cInf h = cInf κ ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w κ) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E k
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1, by rw [mul_one], by rw [map_one, hinf], fun w hw => ?_, fun w _ _ => map_one _⟩
    rcases hw with hw | hw
    · rw [map_one, hS w hw]
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl k w (cLoc w κ), ?_, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · have e := congrArg (fun ψ : XB E k => ψ (g * h)) (hfix w hwS _ (hint w))
        simp only [Rt_apply] at e
        rw [← mul_assoc, e, hf0]
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')


open jumpWindows.GeneralLinearEntryConvergence in
theorem sph (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ) :
    SphOff S (φ : GA E k → ℂ) := by
  intro g κ hinf hS hint
  choose H hH using step hG S φ g κ hfix hinf hS hint
  have hT : Tendsto H atTop (𝓝 κ) := by
    refine tendsto_gl κ H (tendsto_entry S κ H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S κ⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have hc : Continuous fun x : GA E k => φ (g * x) := φ.continuous.comp (continuous_const.mul continuous_id)
  have h1 := (hc.tendsto κ).comp hT
  have h2 : Tendsto ((fun x : GA E k => φ (g * x)) ∘ H) atTop (𝓝 (φ g)) := by
    have e : (fun x : GA E k => φ (g * x)) ∘ H = fun _ => φ g := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end SphericalFunctionIntegral

theorem spherical_function_of : jumpWindows.G0 → jumpWindows.G5 → C0 → K7 → K8 := by
  intro hG0 hG5 hC0 hK7 E _ _ _ k ψ hψ S hcond α φ hgood hsat
  obtain ⟨-, hrt, -, hreg⟩ := hG5 E k ψ hψ
  have hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ :=
    fun w hw x hx => SphericalFunctionIntegral.fix (hsat ⟨w, hw⟩) hx
  have hφ := SphericalFunctionIntegral.sph hG0 S φ hfix
  have hcont := (hreg φ hgood).1
  refine ⟨hφ, fun g κ hinf hS hint => ?_, fun g hg => ⟨fun g₀ hi hS hIn h0 => ?_, fun w hw => ?_⟩⟩
  · have e : Rt E k κ φ = φ := by
      ext x
      simp only [Rt_apply]
      exact hφ x κ hinf hS hint
    rw [← hrt, e]
  · refine hg (jumpWindows.convergence_entries_general_linear hG0 E k S (Wh ψ φ) hcont (fun w hw h hh h0 u => ?_) g g₀ hi hS hIn h0)
    obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    rw [hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) h hh u, h0, zero_mul]
  · obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    obtain ⟨g', hg', e, -, -⟩ := (hC0 E k S).2.2.2.2.2.2 w g
    have h1 := hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) g' hg' (cLoc w g)
    rw [← e] at h1
    rw [h1] at hg
    have h2 := right_ne_zero_of_mul hg
    by_contra hA
    apply h2
    rw [sphericalWhittaker, if_neg hA]

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace HeightDropSingle

open scoped NumberField.AdeleRing

theorem euclid_drop {F : Type*} [NormedField F] {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → F)
    (hz : z p = 0) : euclidNorm z = euclidNorm (fun j => z (p.succAbove j)) := by
  simp only [euclidNorm]
  rw [Fin.sum_univ_succAbove _ p, hz]
  simp

theorem sup_drop {F : Type*} [NormedField F] {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → F)
    (hz : z p = 0) : ‖z‖ = ‖fun j => z (p.succAbove j)‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · rw [hz, norm_zero]; exact norm_nonneg _
    · exact norm_le_pi_norm (fun j => z (p.succAbove j)) j
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm z _

theorem adelicNorm_drop {K : Type*} [Field K] [NumberField K] {n : ℕ} (p : Fin (n + 1))
    (y : Fin (n + 1) → 𝔸[K]) (hy : y p = 0) :
    adelicNorm y = adelicNorm (fun j => y (p.succAbove j)) := by
  unfold adelicNorm
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [euclid_drop p (infComp w y) (by show (y p).1 w = 0; rw [hy]; rfl)]
    rfl
  · refine finprod_congr fun v => ?_
    rw [sup_drop p (finComp v y) (by show (y p).2 v = 0; rw [hy]; rfl)]
    rfl

theorem height_single {K : Type*} [Field K] [NumberField K] {n : ℕ} (x : GL (Fin n) 𝔸[K]) (i : Fin n)
    (hx : x.val i = Pi.single i 1) : Reduction.height x (Pi.single i (1 : K)) = 1 := by
  unfold Reduction.height
  have : ratVec (Pi.single i (1 : K)) ᵥ* (x : Matrix (Fin n) (Fin n) 𝔸[K]) = x.val i := by
    ext c
    simp [ratVec, vecMul, dotProduct, Pi.single_apply]
  rw [this, hx, adelicNorm_single_one]

end HeightDropSingle

theorem short_rows_embedding_of : D0 → MinkowskiBoundAlt → K1 → CornerEmbedding → ShortRowsEmbedding := by
  intro hD hG hK1 hK5e E _ _ _ m k hk hkm ι hι
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C, hC⟩ := hG E n (by omega)
  have hDm := hD E (n + 1)
  have hDk := hD E k
  have hDι : ∀ g, Dt (ι g) = Dt g := ((hK5e E (n + 1) k hkm.le).2 ι hι).2.2.2.1
  have hK := (hK1 E (n + 1) (by omega)).2.2.1
  refine ⟨C, fun g u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · obtain ⟨x, hx⟩ : ∃ x, x = u * ι g := ⟨_, rfl⟩
    rw [← hx]
    have hDx : Dt x = Dt g := by rw [hx, hDm.2.1, hDm.2.2.2.2.1 0 u hu, hDι, one_mul]
    have hrow : x.val (Fin.last n) = Pi.single (Fin.last n) 1 := by
      ext c
      rw [hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
      · rw [hu.2.1, one_mul, hι g]
        have hk' : ¬ ((Fin.last n : ℕ) < k ∧ (c : ℕ) < k) := by simp; omega
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply, Pi.single_apply, eq_comm]
      · intro j _ hj
        rw [hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
      · simp
    have hpos := hDk.1 g
    refine (hK x (Pi.single (Fin.last n) 1) fun h => by simpa using congrFun h (Fin.last n)).trans (le_of_eq ?_)
    unfold ht
    rw [HeightDropSingle.height_single x _ hrow, hDx, Real.rpow_neg hpos.le, one_div]
  · obtain ⟨x, hx⟩ : ∃ x, x = u * ι g := ⟨_, rfl⟩
    rw [← hx]
    have hDx : Dt x = Dt g := by rw [hx, hDm.2.1, hDm.2.2.2.2.1 (k + 1) u hu, hDι, one_mul]
    set p : Fin (n + 1) := ⟨k, hkm⟩ with hp
    have hcol : ∀ i, x.val i p = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (Ad E)) i p := by
      intro i
      rw [hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single p]
      · rw [hι g]
        have hk' : ¬ ((p : ℕ) < k ∧ (p : ℕ) < k) := by simp [p]
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_eq, mul_one]
        exact hu.2.2 i p (by simp [p])
      · intro j _ hj
        rw [hι g]
        have hk' : ¬ ((j : ℕ) < k ∧ (p : ℕ) < k) := by simp [p]
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_ne hj, mul_zero]
      · simp
    set M' : Matrix (Fin n) (Fin n) (Ad E) := x.val.submatrix p.succAbove p.succAbove with hM'
    have hdet : M'.det = x.val.det := by
      rw [Matrix.det_succ_column x.val p, Finset.sum_eq_single p]
      · rw [hcol, Matrix.one_apply_eq, mul_one, Even.neg_one_pow ⟨(p : ℕ), rfl⟩, one_mul]
      · intro i _ hi
        rw [hcol, Matrix.one_apply_ne hi, mul_zero, zero_mul]
      · simp
    have hunit : IsUnit M'.det := by
      rw [hdet]; exact (Matrix.GeneralLinearGroup.det x).isUnit
    let g' : GA E n := M'.nonsingInvUnit hunit
    have hDg' : Dt g' = Dt x := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det x := Units.ext hdet
      unfold Dt; rw [this]
    obtain ⟨ξ', hξ'0, hξ'⟩ := hC g'
    let ξ : Fin (n + 1) → E := p.insertNth 0 ξ'
    have hξ0 : ξ ≠ 0 := by
      intro h; apply hξ'0; ext j
      simpa [ξ] using congrFun h (p.succAbove j)
    have hht : Reduction.height x ξ = Reduction.height g' ξ' := by
      unfold Reduction.height
      rw [HeightDropSingle.adelicNorm_drop p]
      · congr 1
        ext c
        simp only [vecMul, dotProduct]
        rw [Fin.sum_univ_succAbove _ p]
        simp [ξ, ratVec, g', M']
        rfl
      · simp only [vecMul, dotProduct]
        rw [Fin.sum_univ_succAbove _ p]
        simp [ξ, ratVec, hcol, Matrix.one_apply_ne (Fin.succAbove_ne p _)]
    have hpos := hDk.1 g
    refine (hK x ξ hξ0).trans ?_
    unfold ht at hξ' ⊢
    rw [hht, hDx]
    rw [hDg', hDx] at hξ'
    have h1 : Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).1 hξ'
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
    calc Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹) := h1
      _ = C * Dt g ^ ((((n + 1 : ℕ) : ℝ) - 1)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) * Dt g ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [mul_assoc, ← Real.rpow_add hpos]
        congr 2
        push_cast
        ring

end PositivityTheory.AdelicQuotientData

end
end
