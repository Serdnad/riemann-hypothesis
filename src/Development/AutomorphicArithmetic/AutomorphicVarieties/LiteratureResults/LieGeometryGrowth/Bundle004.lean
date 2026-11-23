module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.NormEucSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle002
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

@[expose] public section

section

open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem exists_split' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (g : GA E a) :
    ∃ t : ℝ, splitCentre E a t * g = (retractOne g : UpperTheory.V.KernelIndexFullLattice.G1 E a).1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩
  rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm,
    ← map_inv (Reduction.centralSection E a)]
  refine congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]

theorem UpperTheory.V.Lit.Geo.Pf.csBdd :
    UpperTheory.V.Lit.Geo.Pf.CsBdd := by
  intro E _ _ _ a F hF h
  rcases h with ⟨R, hR⟩ | ⟨C, hC⟩
  · obtain ⟨K, hK, hK'⟩ := (qhtFacts E a).2.2.2 R
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.cont.continuousOn
    refine ⟨max M 0, fun g => ?_⟩
    rcases lt_or_ge R (qht g) with hg | hg
    · rw [hR g hg, norm_zero]; exact le_max_right _ _
    · obtain ⟨γ, t, hm⟩ := hK' g hg
      have := hM _ hm
      rw [mul_assoc, hF.left, hF.centre] at this
      exact this.trans (le_max_left _ _)
  · refine ⟨C, fun g => ?_⟩
    obtain ⟨t, ht⟩ := exists_split' g
    rw [← hF.centre t g, ht]
    exact hC _

end
end

section

open UpperTheory.V.Lit.Geo GlobalTheory.CuspRep Filter Topology

theorem UpperTheory.V.Lit.Geo.Pf.csLie :
    UpperTheory.V.Lit.Geo.Pf.CsLie := by
  intro E _ _ _ a φ X ⟨R, hR⟩
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  obtain ⟨h1, -, h3, -⟩ := qhtFacts E a
  obtain ⟨B, hB⟩ := h3 _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image ccont.inv)
  refine ⟨B * R, fun g hg => ?_⟩
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve φ g c X c0 cder
  have hz : (fun t : ℝ => φ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht
    refine hR _ (not_le.1 fun hle => ?_)
    have h := hB (g * infGL E a (c t)) _ ⟨t, ht, rfl⟩
    simp only [Pi.inv_apply, mul_inv_cancel_right] at h
    have hp := h1 (g * infGL E a (c t))
    have hg1 := h1 g
    have hB0 : 0 ≤ B := by
      by_contra hn
      nlinarith [not_le.1 hn]
    exact absurd (h.trans (mul_le_mul_of_nonneg_left hle hB0)) (not_le.2 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

def ScaleFull : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ], Scale (fun x : Λ => ‖x.1‖ ^ 2) (Module.finrank ℝ V)

def ScaleGen : Prop :=
  ∀ (A V : Type) [AddCommGroup A] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (φ : A →+ V)
    (ε : ℝ), 0 < ε → (∀ x, x ≠ 0 → ε ≤ ‖φ x‖) → Scale (fun x => ‖φ x‖ ^ 2) (Module.finrank ℝ V)

def Moment : Prop :=
  ∀ N k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) (q : ι → ℝ), Scale q N →
    (Summable fun i => (1 + q i) ^ k * Real.exp (-Real.pi * q i)) ∧
      ∑' i, (1 + q i) ^ k * Real.exp (-Real.pi * q i) ≤ C * ∑' i, Real.exp (-Real.pi * q i)

def LogTaylor : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Nonempty ι] (q u : ι → ℝ) (ε : ℝ), Scale q N → 0 ≤ ε → ε ≤ 1 / 4 →
    (∀ i, |u i| ≤ ε * q i) →
    |Real.log (∑' i, Real.exp (-Real.pi * (q i + u i))) - Real.log (∑' i, Real.exp (-Real.pi * q i)) +
      Real.pi * ((∑' i, u i * Real.exp (-Real.pi * q i)) / ∑' i, Real.exp (-Real.pi * q i))| ≤ C * ε ^ 2

def MeanLow : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A V : Type) [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V] (φ : A →+ V),
    Function.Injective φ → (Summable fun x => Real.exp (-Real.pi * ‖φ x‖ ^ 2)) →
    (Summable fun x => ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) → 2 ≤ ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) →
    c * ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)

def ThetaUp : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) (q : ι → ℝ) (i₀ : ι) (μ : ℝ), Scale q N → 0 < μ → μ ≤ 1 →
    (∀ i, i ≠ i₀ → μ ≤ q i) → ∑' i, Real.exp (-Real.pi * q i) ≤ C / μ ^ N

def ThetaLow : Prop :=
  ∀ (A V : Type) [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V] (φ : A →+ V),
    (Summable fun x => Real.exp (-Real.pi * ‖φ x‖ ^ 2)) → ∀ v, φ v ≠ 0 →
    Real.exp (-Real.pi) ≤ ‖φ v‖ * ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2)

def QfFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), (∀ x : Fin a → Cinf E, quad 1 x = qf x) ∧
    (∀ (p p' : Matrix (Fin a) (Fin a) (Cinf E)) (c : ℝ) x, quad (p + p') x = quad p x + quad p' x ∧ quad (c • p) x = c * quad p x) ∧
    (∀ (h : Matrix (Fin a) (Fin a) (Cinf E)) x, qf (x ᵥ* h) = quad (h * star h) x) ∧
    (∀ (c : ℝ) (x : Fin a → Cinf E), qf (c • x) = c ^ 2 * qf x) ∧
    (∀ (p : Matrix (Fin a) (Fin a) (Cinf E)) x, |quad p x| ≤ a * ‖toL p‖ * qf x) ∧
    ∀ x : Fin a → Cinf E, ‖x‖ ^ 2 ≤ qf x ∧ qf x ≤ a * Fintype.card (InfinitePlace E) * ‖x‖ ^ 2

def RankOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : Fin a → Cinf E), trF 1 (vecMulVec w (star w)) = qf w ∧
    (∀ M : Herm E a, trF M.1 (vecMulVec w (star w)) ^ 2 ≤ trF M.1 M.1 * qf w ^ 2) ∧
    ∀ x : Fin a → Cinf E, ‖x ⬝ᵥ w‖ ^ 2 ≤ quad (vecMulVec w (star w)) x ∧ quad (vecMulVec w (star w)) x ≤ qf w * qf x ∧
      (x ⬝ᵥ w = 0 → quad (vecMulVec w (star w)) x = 0)

def ScSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ContDiffOn ℝ ∞ (fun y : Lie E a => sc (Matrix.of y)) (invSet E a) ∧ sc (1 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 ∧
    (∀ X : Lie E a, fderiv ℝ (fun y : Lie E a => sc (Matrix.of y)) (oneL E a) X = -ell E a X) ∧
    (∀ h : GL (Fin a) (Cinf E), sc (h.val * star h.val) = sc h.val ^ 2) ∧ ∀ k : Kinf E a, sc k.1 = 1

def ScTaylor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ Y : Matrix (Fin a) (Fin a) (Cinf E), ‖toL Y‖ ≤ ε →
    |sc (1 + Y) - 1 + ell E a (toL Y)| ≤ C * ‖toL Y‖ ^ 2

def RootEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ ε C : ℝ, 0 < ε ∧ ∀ Y : Herm E a, ‖toL Y.1‖ ≤ ε → ∃ h : GL (Fin a) (Cinf E),
    h.val * star h.val = 1 + Y.1 ∧ ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C

def PolyBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ P ∈ poly E a, ContDiff ℝ ∞ P ∧ (∃ (C : ℝ) (k : ℕ), ∀ x, ‖P x‖ ≤ C * (1 + qf x) ^ k) ∧
    ∀ T : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E), (fun x => fderiv ℝ P x (T x)) ∈ poly E a ∧ (fun x => P (T x)) ∈ poly E a ∧
      ∀ u, (fun x => fderiv ℝ P x u) ∈ poly E a

def PolyD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ P ∈ poly E a, ContDiff ℝ ∞ (pg P) ∧
    (∃ (C : ℝ) (k : ℕ), ∀ x, ‖fderiv ℝ (pg P) x‖ ≤ C * (1 + qf x) ^ k * gauss x) ∧
    ∀ T : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E), ∃ Q ∈ poly E a, ∀ x, fderiv ℝ (pg P) x (T x) = pg Q x

def SumDer : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ι : Type) (x : ι → Fin a → Cinf E) (N : ℕ), Scale (fun i => qf (x i)) N → ∀ P ∈ poly E a, ∀ y ∈ invSet E a,
    (Summable fun i => pg P (x i ᵥ* Matrix.of y)) ∧ DifferentiableAt ℝ (msum x P) y ∧
      ∀ Z : Lie E a, fderiv ℝ (msum x P) y Z = ∑' i, fderiv ℝ (pg P) (x i ᵥ* Matrix.of y) (x i ᵥ* Matrix.of Z)

def SumSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ι : Type) (x : ι → Fin a → Cinf E) (N : ℕ), Scale (fun i => qf (x i)) N → ∀ P ∈ poly E a,
    ContDiffOn ℝ ∞ (msum x P) (invSet E a)

def LatEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∃ L : AddSubgroup (Fin a → Af E), IsLat L ∧ ∀ u ∈ U, ∀ x ∈ L, x ᵥ* u.val ∈ L

def LatMin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ (C : ℝ) (N : ℕ), 1 ≤ C ∧ ∀ g : GA E a, ∀ v ∈ lat L g, v ≠ 0 →
    1 ≤ C * AutomorphicForm.height (K := E) g ^ N * qf (pt g v)

def LatScale : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ N : ℕ, ∀ g : GA E a, Scale (fun v : lat L g => qf (pt (rt g) v.1)) N

def RtFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → (∀ γ t (g : GA E a), rt (ratGL E a γ * splitCentre E a t * g) = ratGL E a γ * rt g) ∧
    (∀ g : GA E a, rt (rt g) = rt g ∧ qht (rt g) = qht g ∧ ptF (rt g) = ptF g) ∧
    (∀ (γ : GL (Fin a) E) (g : GA E a) v, ptF (ratGL E a γ * g) v = ptF g (v ᵥ* γ.val) ∧ pt (ratGL E a γ * g) v = pt g (v ᵥ* γ.val)) ∧
    ∀ U : Subgroup (GL (Fin a) (Af E)), IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ u ∈ U, ∀ g : GA E a,
      rt (g * finGL E a u) = rt g * finGL E a u

def RtInf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (g : GA E a) (h : GL (Fin a) (Cinf E)) v,
    pt (rt (g * infGL E a h)) v = sc h.val • (pt (rt g) v ᵥ* h.val)

def SumInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (L : AddSubgroup (Fin a → Af E)) (M : Type) [AddCommMonoid M] [TopologicalSpace M] (F : (Fin a → Cinf E) → M),
    (∀ γ t g, gsum L F (ratGL E a γ * splitCentre E a t * g) = gsum L F g) ∧
    (∀ g (h : GL (Fin a) (Cinf E)), gsum L F (g * infGL E a h) = ∑' v : lat L g, F (sc h.val • (pt (rt g) v.1 ᵥ* h.val))) ∧
    ∀ U : Subgroup (GL (Fin a) (Af E)), IsCompact (U : Set (GL (Fin a) (Af E))) → (∀ u ∈ U, ∀ x ∈ L, x ᵥ* u.val ∈ L) →
      ∀ u ∈ U, ∀ g, gsum L F (g * finGL E a u) = gsum L F g

def FnInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (L : AddSubgroup (Fin a → Af E)),
    (∀ γ t g, fn L (ratGL E a γ * splitCentre E a t * g) = fn L g ∧ dev L (ratGL E a γ * splitCentre E a t * g) = dev L g) ∧
    (∀ U : Subgroup (GL (Fin a) (Af E)), IsCompact (U : Set (GL (Fin a) (Af E))) → (∀ u ∈ U, ∀ x ∈ L, x ᵥ* u.val ∈ L) →
      ∀ u ∈ U, ∀ g, fn L (g * finGL E a u) = fn L g ∧ dev L (g * finGL E a u) = dev L g) ∧
    ∀ (k : Kinf E a) g, Th L (g * infGL E a (Unitary.toUnits k)) = Th L g

def DevCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∀ (k : Kinf E a) g, adHerm k (dev L (g * infGL E a (Unitary.toUnits k))) = dev L g

def MeanBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → (∀ g, 1 ≤ Th L g ∧ gsum L (pg 1) g = (Th L g : ℝ)) ∧ ∀ P ∈ poly E a,
    (∀ g, Summable fun v : lat L g => pg P (pt (rt g) v.1)) ∧ ∃ C : ℝ, ∀ g, ‖mean L P g‖ ≤ C

def ThSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∀ P ∈ poly E a, ∃ φ : Sm E a, φ.1 = gsum L (pg P) ∧
    ∀ X : Lie E a, ∃ Q ∈ poly E a, (lie E a X φ).1 = gsum L (pg Q)

def BddAlg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Set (GA E a → ℂ)), (∀ f ∈ S, (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧
      ∃ φ : Sm E a, φ.1 = f ∧ ∀ X, (lie E a X φ).1 ∈ Algebra.adjoin ℂ S) →
    (∀ f ∈ Algebra.adjoin ℂ S, ∃ φ : Sm E a, φ.1 = f ∧ BddDer φ) ∧
      ∀ ψ : Sm E a, (∀ X, (lie E a X ψ).1 ∈ Algebra.adjoin ℂ S) → BddDer ψ

def MeanSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → (∀ P ∈ poly E a, ∃ φ : Sm E a, φ.1 = mean L P ∧ ∀ X, (lie E a X φ).1 ∈ meanAlg L) ∧
    ∃ φ : Sm E a, (∀ g, φ.1 g = fn L g) ∧ ∀ X, (lie E a X φ).1 ∈ meanAlg L

def MomQuad : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∀ g (p : Matrix (Fin a) (Fin a) (Cinf E)),
    trF (mom L g).1 p = (∑' v : lat L g, quad p (pt (rt g) v.1) * gauss (pt (rt g) v.1)) / Th L g

def DevFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → (∀ i j w, (fun g => (dev L g).1 i j w) ∈ meanAlg L) ∧
    (∃ B : ℝ, 0 < B ∧ ∀ g, ‖toL (mom L g).1‖ ≤ B ∧ ‖toL (dev L g).1‖ ≤ B ∧ |trF (dev L g).1 (dev L g).1| ≤ B) ∧
    ∀ g, ell E a (toL (dev L g).1) = 0 ∧ trF (mom L g).1 (dev L g).1 = trF (dev L g).1 (dev L g).1

def FnTaylor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ g (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : GL (Fin a) (Cinf E)),
    ell E a (toL Y) = 0 → ‖toL Y‖ ≤ ε → h.val * star h.val = 1 + Y →
    |fn L (g * infGL E a h) - fn L g + Real.pi * trF (mom L g).1 Y| ≤ C * ‖toL Y‖ ^ 2

def SiegelHt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (Ω : Set (GA E a)) (C : ℝ) (N : ℕ), IsCompact Ω ∧ (∀ b ∈ Ω, b ∈ Reduction.adelicBorel (K := E) (n := a)) ∧
    ∀ g : KernelIndexFullLattice.G1 E a, ∃ (γ : GL (Fin a) E) (b k : GA E a) (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), b ∈ Ω ∧
      k ∈ Reduction.maxCompact (K := E) (n := a) ∧
      ratGL E a γ * g.1 = b * Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∧
      ∀ i : Fin a, (i.val + 1 = a → qht (E := E) (a := a) g.1 * ρ i ^ (2 * N) ≤ C) ∧
        (i.val = 0 → qht (E := E) (a := a) g.1 ≤ C * ρ i ^ (2 * N))

def SiegelRow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∃ (T : Set (Fin a → Af E)) (C : ℝ) (N : ℕ), IsCompact T ∧ ∀ g : KernelIndexFullLattice.G1 E a, ∃ v : Fin a → E, v ≠ 0 ∧
    ptF (E := E) (a := a) g.1 v ∈ T ∧ qht (E := E) (a := a) g.1 * qf (pt (E := E) (a := a) g.1 v) ^ N ≤ C

def SiegelCol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∃ (T : Set (Fin a → Af E)) (C : ℝ) (N : ℕ), IsCompact T ∧ ∀ g : KernelIndexFullLattice.G1 E a, ∃ ξ : Fin a → E, ξ ≠ 0 ∧
    (GeneralLinearGroup.map (pFin E) (g.1⁻¹ : GA E a)).val *ᵥ vFin ξ ∈ T ∧
    qht (E := E) (a := a) g.1 * qf ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf ξ) ^ N ≤ C

def ShortRow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ (C : ℝ) (N : ℕ), ∀ g : GA E a, ∃ v ∈ lat L g, v ≠ 0 ∧ qht g * qf (pt (rt g) v) ^ N ≤ C

def ShortCol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ (c C : ℝ) (N : ℕ), 0 < c ∧ ∀ g : GA E a, ∃ w : Fin a → Cinf E, w ≠ 0 ∧ qht g * qf w ^ N ≤ C ∧
    ∀ v ∈ lat L g, pt (rt g) v ⬝ᵥ w = 0 ∨ c ≤ ‖pt (rt g) v ⬝ᵥ w‖

def FnLe : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ C : ℝ, ∀ g, fn L g ≤ C * (1 + Real.log (qht g))

def LeFn : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ C : ℝ, ∀ g, Real.log (qht g) ≤ C * (1 + fn L g)

def GradA : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ c : ℝ, 0 < c ∧ ∀ g, 2 ≤ Th L g → c ≤ ell E a (toL (mom L g).1)

def GradB : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ C : ℝ, ∀ g (w : Fin a → Cinf E) (c : ℝ), 0 < c →
    (∀ v ∈ lat L g, pt (rt g) v ⬝ᵥ w = 0 ∨ c ≤ ‖pt (rt g) v ⬝ᵥ w‖) →
    trF (mom L g).1 (vecMulVec w (star w)) ≤ C * qf w ^ 2 / c ^ 2

def Grad : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ c f₀ : ℝ, 0 < c ∧ ∀ g, f₀ ≤ fn L g → c ≤ trF (dev L g).1 (dev L g).1

end UpperTheory.V.Lit.Geo
end
end
