module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConj
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernTransgression_forms_frame_invariant : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' G₂ G₂' T K K' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K' u a b) x) → IsUnit (K' v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ ∧ G₂' x = T x * G' x * (K' x)ᴴ) → ∀ k, powAt G₂ v k = powAt G v k ∧ chernAt G₂ v k = chernAt G v k ∧ transAt G₂ G₂' v k = transAt G G' v k := by
  first | exact @GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame | exact GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame | (intros; apply GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.curvatureMatrixEvenForms_entries_smooth_coefficients : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, (∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b)) ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) v) := by
  first | exact @GlobalTheory.CurvSmooth.curvEv_entry_smooth | exact GlobalTheory.CurvSmooth.curvEv_entry_smooth | (intros; apply GlobalTheory.CurvSmooth.curvEv_entry_smooth <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.dbar_curvatureMatrixEvenForms_eq_zero : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => (curvEv G x i j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv | exact GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv | (intros; apply GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth : ∀ (n s : ℕ) (G : V n → Matrix (Fin s) (Fin s) ℂ) (v : V n), MContDiffAt ∞ G v → (G v).PosDef → MContDiffAt ∞ (fun x => ldPart (G x)) v ∧ ∀ i, ContDiffAt ℝ ∞ (fun x => grD (G x) i) v := by
  first | exact @GlobalTheory.ChernCalc.ldPart_grD_smooth | exact GlobalTheory.ChernCalc.ldPart_grD_smooth | (intros; apply GlobalTheory.ChernCalc.ldPart_grD_smooth <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (s : ℕ) (T : Matrix (Fin s) (Fin s) X.Fn) (y : CxPts X.str σ), (∀ i j, RegAt (under y) (T i j)) → T.det ≠ 0 → RegAt (under y) (T.det)⁻¹ → HolUnitAt (atlas X σ) (fun z => T.map (ratVal · z)) y := by
  first | exact @GlobalTheory.ChernCalc.holUnitAt_ratVal | exact GlobalTheory.ChernCalc.holUnitAt_ratVal | (intros; apply GlobalTheory.ChernCalc.holUnitAt_ratVal <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  first | exact @GlobalTheory.ChernCalc.TopPow.part_c1W_pow | exact GlobalTheory.ChernCalc.TopPow.part_c1W_pow | (intros; apply GlobalTheory.ChernCalc.TopPow.part_c1W_pow <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (z : CxPts Y.str σ), under (ptMap σ f hf z) = f (under z) ∧ ∀ A ∈ E.S (f (under z)), ∀ B ∈ E'.S (under z), ∀ τ, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ * H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
  first | exact @GlobalTheory.ChernCalc.pullGram_eq_of_frame | exact GlobalTheory.ChernCalc.pullGram_eq_of_frame | (intros; apply GlobalTheory.ChernCalc.pullGram_eq_of_frame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernForm_newton_identities_curvature_power_sums : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), chernAt G v 0 = 1 ∧ ∀ j : ℕ, (j : ℂ) • chernAt G v j = -∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powAt G v (i + 1) * chernAt G v (j - 1 - i)) := by
  first | exact @GlobalTheory.ChernCalc.chernAt_newton | exact GlobalTheory.ChernCalc.chernAt_newton | (intros; apply GlobalTheory.ChernCalc.chernAt_newton <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem grWeight_frame_indep : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ B ∈ E.S (genericPoint X.X), ∀ (y : CxPts X.str σ),
    ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ (x : Root m) (f : X.Fn), UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f) →
      -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
        -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  first
  | exact @_root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep
  | exact _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep
  | (apply _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep ..)

end GlobalTheory.ChernCalc
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj : ∀ (s : ℕ) (G g : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ i j, i < j → g i j = 0) → IsUnit g.det → ldPart (g * G * gᴴ) = g * ldPart G * (Matrix.diagonal fun i => g i i)ᴴ ∧ ∀ i, grD (g * G * gᴴ) i = ‖g i i‖ ^ 2 * grD G i := by
  first | exact @GlobalTheory.ChernCalc.ldPart_conj_lower | exact GlobalTheory.ChernCalc.ldPart_conj_lower | (intros; apply GlobalTheory.ChernCalc.ldPart_conj_lower <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.ShiftMono

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem shift_apply_zero (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

theorem shift_apply_succ (u : Fin G.N → F) (x : Tot G) (j : ℕ) : shift G u x (j + 1) = G.mulW j u (x j) := rfl

theorem mulW_comm (j : ℕ) (u v : Fin G.N → F) (m : G.Sec j) :
    G.mulW (j + 1) u (G.mulW j v m) = G.mulW (j + 1) v (G.mulW j u m) := by
  simp only [G.mulW_apply]
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]
  ring

theorem shift_comm (u v : Fin G.N → F) : shift G u * shift G v = shift G v * shift G u := by
  refine LinearMap.ext fun x => funext fun j => ?_
  rcases j with _ | _ | j
  · rfl
  · show G.mulW 0 u (shift G v x 0) = G.mulW 0 v (shift G u x 0)
    rw [shift_apply_zero, shift_apply_zero, map_zero, map_zero]
  · exact mulW_comm G j u v (x j)

theorem shift_single (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext k
  rcases k with _ | k
  · rw [shift_apply_zero, Pi.single_eq_of_ne (by omega)]
  · rw [shift_apply_succ]
    by_cases hk : k = j
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (by omega), map_zero]

variable (s : Fin G.D → Fin G.N → F)

def mono (α : Fin G.D →₀ ℕ) {j l : ℕ} (h : j + α.degree = l) : G.Sec j →ₗ[F] G.Sec l :=
  mulMono (isLB_tens G.K.isLB G.isLBA) G.isLB (G.sec s) (⟨α, rfl⟩ : MonoDeg (Fin G.D) α.degree)
    ((Nat.cast_add j _).symm.trans (congrArg _ h))

theorem mono_add (α β γ : Fin G.D →₀ ℕ) (e : γ = α + β) {j l' l : ℕ} (h : j + γ.degree = l)
    (h₂ : j + β.degree = l') (h₁ : l' + α.degree = l) (m : G.Sec j) :
    mono G s γ h m = mono G s α h₁ (mono G s β h₂ m) := by
  subst e
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_add]
  ring

theorem mono_zero (α : Fin G.D →₀ ℕ) (e : α = 0) {j : ℕ} (h : j + α.degree = j) (m : G.Sec j) :
    mono G s α h m = m := by
  subst e
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_zero, one_mul]

theorem mono_single (i : Fin G.D) {j : ℕ} (h : j + (Finsupp.single i 1).degree = j + 1) (m : G.Sec j) :
    mono G s (Finsupp.single i 1) h m = G.mulW j (s i) m := by
  rw [G.mulW_apply]
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_single, pow_one]

def Acts (E : Module.End F (Tot G)) (α : Fin G.D →₀ ℕ) : Prop :=
  ∀ (j l : ℕ) (h : j + α.degree = l) (m : G.Sec j), E (Pi.single j m) = Pi.single l (mono G s α h m)

theorem acts_one : Acts G s 1 0 := fun j l h m => by
  obtain rfl : j = l := by simpa using h
  rw [mono_zero G s 0 rfl h m]; rfl

theorem acts_mul {E₁ E₂ : Module.End F (Tot G)} {α₁ α₂ : Fin G.D →₀ ℕ} (h₁ : Acts G s E₁ α₁) (h₂ : Acts G s E₂ α₂) :
    Acts G s (E₁ * E₂) (α₁ + α₂) := fun j l h m => by
  have h' : j + α₂.degree + α₁.degree = l := by rw [map_add (f := _)] at h; omega
  rw [Module.End.mul_apply, h₂ j (j + α₂.degree) rfl m, h₁ (j + α₂.degree) l h',
    ← mono_add G s α₁ α₂ (α₁ + α₂) rfl]

theorem acts_shift (i : Fin G.D) : Acts G s (shift G (s i)) (Finsupp.single i 1) := fun j l h m => by
  obtain rfl : l = j + 1 := by simpa using h.symm
  rw [shift_single, mono_single]

theorem acts_pow (i : Fin G.D) (k : ℕ) : Acts G s (shift G (s i) ^ k) (Finsupp.single i k) := by
  induction k with
  | zero => simpa using acts_one G s
  | succ k ih =>
    rw [pow_succ, show Finsupp.single i (k + 1) = Finsupp.single i k + Finsupp.single i 1 by simp]
    exact acts_mul G s ih (acts_shift G s i)

theorem acts_list : ∀ (n : ℕ) (E : Fin n → Module.End F (Tot G)) (g : Fin n → Fin G.D →₀ ℕ),
    (∀ i, Acts G s (E i) (g i)) → Acts G s (List.ofFn E).prod (∑ i, g i)
  | 0, E, g, _ => by simpa using acts_one G s
  | n + 1, E, g, hE => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact acts_mul G s (hE 0) (acts_list n _ _ fun i => hE i.succ)

theorem acts_pw (α : Fin G.D →₀ ℕ) : Acts G s (HSShort.pw (shift G) s α) α := by
  have := acts_list G s G.D (fun i => shift G (s i) ^ α i) (fun i => Finsupp.single i (α i))
    fun i => acts_pow G s i (α i)
  rwa [Finsupp.univ_sum_single] at this

end GlobalTheory.HSShort.ShiftMono

namespace GlobalTheory.HSShort

theorem shift_comm_single_mono : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F),
    (∀ u v, shift G u * shift G v = shift G v * shift G u) ∧ (∀ (j : ℕ) u (m : G.Sec j), shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m)) ∧ ∀ (s : Fin G.D → Fin G.N → F) (a j l : ℕ) (h : j + a = l) (α : MonoDeg (Fin G.D) a) (m : G.Sec j), pw (shift G) s α.1 (Pi.single j m) = Pi.single l (mulPow G s h α m) := by
  intro F _ _ G
  refine ⟨ShiftMono.shift_comm G, ShiftMono.shift_single G, fun s a j l h α m => ?_⟩
  obtain ⟨α, rfl⟩ := α
  exact ShiftMono.acts_pw G s α j l h m

end GlobalTheory.HSShort
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.HSShort.GlobWord

theorem shift_single {K : Type} [Field K] [NumberField K] (G : Geo K) (j : ℕ) (u : Fin G.N → K) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext i
  cases i with
  | zero => rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j).symm]; rfl
  | succ i =>
    show G.mulW i u ((Pi.single j m : Tot G) i) = _
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (Nat.succ_injective h')), map_zero]

theorem word_global : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (t j : ℕ) (u : Fin t → Fin G.N → K), ∀ x ∈ G.global j, ∃ x' ∈ G.global (j + t), word (shift G) u (Pi.single j x) = Pi.single (j + t) x' ∧ ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s) (δ : ℕ) (Co : Coord G hs δ) (p : Fin δ), Co.ev (j + t) (hs.res (j + t) x') p = (∏ q, ∑ k, u q k * Co.y p k) * Co.ev j (hs.res j x) p := by
  intro K _ _ G t j
  induction t with
  | zero =>
    intro u x hx
    exact ⟨x, hx, by simp [word], fun s hs δ Co p => by simp⟩
  | succ t ih =>
    intro u x hx
    obtain ⟨x', hx', hw, hr⟩ := ih (fun q => u q.succ) x hx
    refine ⟨G.mulW (j + t) (u 0) x', GlobalTheory.HilbertSamuel.Model.mulW_mem_global G (j + t) _ hx', ?_, fun s hs δ Co p => ?_⟩
    · unfold word at hw ⊢
      rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, hw]
      exact shift_single G (j + t) (u 0) x'
    · show Co.ev (j + t + 1) (hs.res (j + t + 1) (G.mulW (j + t) (u 0) x')) p = _
      rw [hs.res_mulW, Co.mul]
      beta_reduce
      rw [hr, Fin.prod_univ_succ, mul_assoc]

end GlobalTheory.HSShort.GlobWord
end
