module

public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle148
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle164
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle147
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_capelliFold_norm_le : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Z : B.Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), B.CkOn ⊤ (B.GV k r) X → B.CCle A (5 + w.length * (2 * r + k + 1)) X c → B.CCle A 5 Z c' → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z‖ ≤ C * c * c' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA
  obtain ⟨_, _, _, ⟨C, hC⟩, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq Bs A hA
  obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.capelliWordProduct_decayBound_uniform k r Wp Wq s w 5
  refine ⟨|C| * K, mul_nonneg (abs_nonneg _) hK0, ?_⟩
  intro X Z c c' hX hc hc'
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  have hc0' : 0 ≤ c' := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc'
  have hF := hK A c X hX hc
  have h := (hC _ _ _ _ ⟨_, hF⟩ ⟨_, hc'⟩ (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (by norm_num) hF)
    (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (by norm_num) hc')).2.2
  refine h.trans ?_
  rw [mul_assoc |C| K c]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hK0 hc0)) hc0'

end GlobalTheory
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem capelli_eigenSum_linearCombination : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ι : Type) (S : Finset ι) (co : ι → ℂ) (Fs : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ x ∈ S, ∃ (d' : ℕ) (A' : ℝ), d' ≤ d ∧ A ≤ A' ∧ (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d' : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A') m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (Fs x) g = ∑ i, Fi i g)) → (∀ g ∈ B.GV k r, F g = ∑ x ∈ S, co x • Fs x g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A ι S co Fs F h hF
  classical
  have h' : ∀ x : S, _ := fun x => h x.1 x.2
  choose d' A' hd hA N Fi ν hν hC hE hS using h'
  let e := (Fintype.equivFin (Σ x : S, Fin (N x))).symm
  refine ⟨_, fun j g => co (e j).1 • Fi (e j).1 (e j).2 g, fun j => ν (e j).1 (e j).2, ?_, ?_, ?_, ?_⟩
  · intro j s
    exact (hν _ _ s).trans (by exact_mod_cast hd _)
  · intro j
    refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul _ (hC _ _).1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono (hA (e j).1) le_rfl ((hC _ (e j).2).2 m)
    exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul _ hc⟩
  · intro j Y g hg
    have h1 := Formalism.FourierDecayAlt.P.CutMP.En.cV_smul (k := k) (r := r) (Y : ℂ) (co (e j).1) (Fi (e j).1 (e j).2)
    have h2 := congrFun h1 g
    have h3 : (fun g => co (e j).1 • Fi (e j).1 (e j).2 g) = co (e j).1 • Fi (e j).1 (e j).2 := rfl
    beta_reduce
    rw [h3, h2, Pi.smul_apply, hE _ _ Y g hg, smul_comm]
  · intro g hg
    rw [hF g hg, Equiv.sum_comp e (fun y : (Σ x : S, Fin (N x)) => co y.1 • Fi y.1 y.2 g),
      Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hS x g hg, Finset.smul_sum]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_integralExpansions_of_valuation_ge : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (q : ℕ), 1 ≤ q → ∀ (s : Fam D.toPre F q) (r : ℚ), (∀ χ, VGe D F v q χ (s.s χ) r) → ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α), (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i)) ∧ (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε q) (s.s α) (D.toPre.famφB α) (DegPre.famε q) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  first | exact @GlobalTheory.exists_integral_expansions_of_vge | exact GlobalTheory.exists_integral_expansions_of_vge | (intros; apply GlobalTheory.exists_integral_expansions_of_vge <;> assumption)
end
