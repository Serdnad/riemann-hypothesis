module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle224
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle389
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.discreteSeries_gKMap_values_eq_generalisedCoefficients : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := by
  first | exact @GlobalTheory.TypeSum.GKCoef.values_eq_coef | exact GlobalTheory.TypeSum.GKCoef.values_eq_coef | (intros; apply GlobalTheory.TypeSum.GKCoef.values_eq_coef <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeSum.KSeries

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem coef_eq_fam (h : Std ε σ) {p : ℕ} {ℓ : Fin p → (H →ₗ[ℂ] ℂ)} {x : Fin p → H}
    (hℓ : ∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) (hx : ∀ j, Sm ε σ (x j)) {Φ : List (Mx n) → Mx n → ℂ}
    (h0 : ∀ y ∈ UJset ε, Φ [] y = ∑ j, ℓ j (σ y (x j)))
    (hd : ∀ (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
      ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ l (y * NormedSpace.exp (t • X))) (Φ (X :: l) y) 0) :
    ∀ w : List (Mx n), (∀ Y ∈ w, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ y ∈ UJset ε,
      Φ w y = ∑ j, ℓ j (σ y (Dw σ w (x j))) := by
  intro w
  induction w with
  | nil => intro _ y hy; simpa [Dw] using h0 y hy
  | cons X l ih =>
    intro hw y hy
    have hX := hw X List.mem_cons_self
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hlL : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hl Y hY).1
    have d1 := hd l hl X hX.1 hX.2 y hy
    have d2 : HasDerivAt (fun t : ℝ => ∑ j, ℓ j (σ (y * NormedSpace.exp (t • X)) (Dw σ l (x j))))
        (∑ j, ℓ j (σ (y * NormedSpace.exp ((0 : ℝ) • X)) (dRep σ X (Dw σ l (x j))))) 0 :=
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ => GlobalTheory.TypeSum.CoefLow.hasDerivAt_coef h (hℓ j) ((hx j).word h.1 hlL) hX.1 hy 0
    have e : (fun t : ℝ => Φ l (y * NormedSpace.exp (t • X))) =
        fun t => ∑ j, ℓ j (σ (y * NormedSpace.exp (t • X)) (Dw σ l (x j))) := by
      funext t; exact ih hl _ (mul_mem_UJ hy (exp_mem_UJ hX.1 t))
    rw [e] at d1
    rw [d1.unique d2]
    simp [Dw]

end GlobalTheory.TypeSum.KSeries

namespace GlobalTheory.TypeSum.KSeries

def pad {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) : ℕ × ℕ → α :=
  fun p => if h : p.2 < q p.1 then a p.1 ⟨p.2, h⟩ else 0

theorem pad_of_lt {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) {i r : ℕ} (h : r < q i) :
    pad q a (i, r) = a i ⟨r, h⟩ := dif_pos h

theorem pad_of_ge {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) {i r : ℕ} (h : ¬ r < q i) :
    pad q a (i, r) = 0 := dif_neg h

theorem pad_hasSum_fiber {α : Type} [AddCommMonoid α] [TopologicalSpace α] (q : ℕ → ℕ)
    (a : (i : ℕ) → Fin (q i) → α) (i : ℕ) : HasSum (fun r => pad q a (i, r)) (∑ r, a i r) := by
  have h1 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := Finset.range (q i))
    (f := fun r => pad q a (i, r)) (fun r hr => pad_of_ge q a fun h => hr (Finset.mem_range.2 h))
  convert h1 using 1
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun r _ => (pad_of_lt q a r.isLt).symm

theorem pad_summable (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → ℝ) (ha : ∀ i r, 0 ≤ a i r) (b : ℕ → ℝ)
    (hb : Summable b) (hle : ∀ i, ∑ r, a i r ≤ b i) : Summable (pad q a) := by
  have nn : 0 ≤ pad q a := fun p => by
    simp only [pad, Pi.zero_apply]; split_ifs
    · exact ha _ _
    · exact le_rfl
  rw [summable_prod_of_nonneg nn]
  refine ⟨fun i => (pad_hasSum_fiber q a i).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => tsum_nonneg fun r => nn _) (fun i => ?_) hb
  rw [(pad_hasSum_fiber q a i).tsum_eq]
  exact hle i

theorem pad_hasSum (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → ℂ) (hs : Summable fun p => ‖pad q a p‖) {F : ℂ}
    (hF : HasSum (fun i => ∑ r, a i r) F) : HasSum (pad q a) F := by
  have hs' : Summable (pad q a) := hs.of_norm
  have h3 : ∑' p, pad q a p = F := (hs'.hasSum.prod_fiberwise (pad_hasSum_fiber q a)).unique hF
  rw [← h3]
  exact hs'.hasSum

end GlobalTheory.TypeSum.KSeries

namespace GlobalTheory.TypeSum.KSeries


theorem hasTypeAll_of_kTypes : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (x : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, IsKFin ε σ (x j)) ∧
        ∀ y ∈ UJset ε, (∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) = ∑ j, ℓ j (σ y (x j))) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.SmoothGlob.lieSet ε) (UJset ε) σ f := by
  intro hHC hCW n ε H _ _ _ σ hσ f hf hU hyp
  obtain ⟨e, he1, he2, hP⟩ := GlobalTheory.T.exists_rightKFourierSeries_unitary_moderateGrowth n ε
  obtain ⟨N, Φ, B, hΦ0, hΦd, hΦb, hBs, hsum⟩ := hP f hf hU
  obtain ⟨S, hS, m, A, hQ⟩ := GlobalTheory.T.exists_common_growth_exponent_gK_discreteSeries hHC hCW n ε H σ hσ N
  choose p ℓ x hℓ hx heq using fun i => hyp (e i) (he1 i) (he2 i)
  have hbound : ∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ i j (σ y (Dw σ w (x i j)))‖ ≤ B i k * (1 + hs y) ^ N := by
    intro i k w hk hw y hy
    rw [← coef_eq_fam hσ (hℓ i) (fun j => hσ.2.2.1 _ (hx i j)) (fun y hy => (hΦ0 i y hy).trans (heq i y hy))
      (hΦd i) w (fun Y hY => ⟨(hw Y hY).1, (hw Y hY).2.1⟩) y hy]
    exact hΦb i k w hk hw y hy
  choose q ℓ' x' c hx' hc hℓ' hsumS heq' using fun i => hQ (p i) (ℓ i) (x i) (hℓ i) (hx i) (B i) (hbound i)
  obtain ⟨S₁, hS₁, -, ⟨Bc, hBc, hctrl⟩, A₀, hA₀, hdom⟩ := GlobalTheory.TypeSumCtrl.exists_ctrl n ε H σ hσ S hS
  have hV : ∀ a, Sm ε σ (pad q x' a) := fun a => by
    simp only [pad]; split_ifs
    · exact hx' _ _
    · exact sm_iff.2 (Submodule.zero_mem _)
  have key : ∀ S', Words (lieSet ε) S' →
      Summable (fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a)) := by
    intro S' hS'
    have e1 : (fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a)) =
        pad q (fun i r => A₀ * c i r * sobNorm σ S' (x' i r)) := by
      funext a; simp only [pad]; split_ifs <;> simp
    rw [e1]
    refine pad_summable q _ (fun i r => mul_nonneg (mul_nonneg hA₀ (hc i r)) (sobNorm_nonneg _ _ _))
      (fun i => A₀ * A S' * B i (m S')) ((hBs (m S')).mul_left (A₀ * A S')) fun i => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hsumS i S' hS') hA₀
  have hnorm : ∀ g ∈ UJset ε, ∀ a, ‖pad q (fun i r => ℓ' i r (σ g (x' i r))) a‖ ≤
      Bc g * (pad q (fun i r => A₀ * c i r) a * sobNorm σ S₁ (pad q x' a)) := by
    intro g hg a
    simp only [pad]
    split_ifs with h
    · have hs1 := (hx' a.1 ⟨a.2, h⟩).translate hσ.1 hg
      calc ‖ℓ' a.1 ⟨a.2, h⟩ (σ g (x' a.1 ⟨a.2, h⟩))‖
          ≤ c a.1 ⟨a.2, h⟩ * sobNorm σ S (σ g (x' a.1 ⟨a.2, h⟩)) := hℓ' _ _ _ hs1
        _ ≤ c a.1 ⟨a.2, h⟩ * (A₀ * sobNorm σ S₁ (σ g (x' a.1 ⟨a.2, h⟩))) :=
          mul_le_mul_of_nonneg_left (hdom _ hs1) (hc _ _)
        _ ≤ c a.1 ⟨a.2, h⟩ * (A₀ * (Bc g * sobNorm σ S₁ (x' a.1 ⟨a.2, h⟩))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hctrl g hg _ (hx' _ _)) hA₀) (hc _ _)
        _ = Bc g * (A₀ * c a.1 ⟨a.2, h⟩ * sobNorm σ S₁ (x' a.1 ⟨a.2, h⟩)) := by ring
    · simp
  have hterm : ∀ g a, pad q ℓ' a (σ g (pad q x' a)) = pad q (fun i r => ℓ' i r (σ g (x' i r))) a := by
    intro g a; simp only [pad]; split_ifs <;> simp
  have hsum2 : ∀ g ∈ UJset ε, HasSum (fun a : ℕ × ℕ => pad q ℓ' a (σ g (pad q x' a))) (f g) := by
    intro g hg
    simp only [hterm]
    refine pad_hasSum q _ (Summable.of_nonneg_of_le (fun a => norm_nonneg _) (hnorm g hg)
      ((key S₁ hS₁).mul_left (Bc g))) ?_
    refine (hsum g hg).congr_fun fun i => ?_
    rw [heq i g hg, heq' i g hg]
  refine ⟨S₁, hS₁, ⟨Bc, hBc, hctrl⟩, pad q x' ∘ Nat.pairEquiv.symm, pad q ℓ' ∘ Nat.pairEquiv.symm,
    pad q (fun i r => A₀ * c i r) ∘ Nat.pairEquiv.symm, ⟨⟨fun k => hV _, fun k => ?_, fun k w hw => ?_, ?_, fun g hg => ?_⟩, fun S' hS' => ?_⟩⟩
  · show 0 ≤ pad q (fun i r => A₀ * c i r) (Nat.pairEquiv.symm k)
    simp only [pad]; split_ifs
    · exact mul_nonneg hA₀ (hc _ _)
    · exact le_rfl
  · show ‖pad q ℓ' (Nat.pairEquiv.symm k) w‖ ≤ pad q (fun i r => A₀ * c i r) (Nat.pairEquiv.symm k) * sobNorm σ S₁ w
    simp only [pad]; split_ifs with h
    · calc ‖ℓ' _ _ w‖ ≤ c _ ⟨_, h⟩ * sobNorm σ S w := hℓ' _ _ _ hw
        _ ≤ c _ ⟨_, h⟩ * (A₀ * sobNorm σ S₁ w) := mul_le_mul_of_nonneg_left (hdom _ hw) (hc _ _)
        _ = A₀ * c _ ⟨_, h⟩ * sobNorm σ S₁ w := by ring
    · simp
  · exact (Nat.pairEquiv.symm.summable_iff (f := fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S₁ (pad q x' a))).2 (key S₁ hS₁)
  · exact (Nat.pairEquiv.symm.hasSum_iff (f := fun a : ℕ × ℕ => pad q ℓ' a (σ g (pad q x' a)))).2 (hsum2 g hg)
  · exact (Nat.pairEquiv.symm.summable_iff (f := fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a))).2 (key S' hS')

end GlobalTheory.TypeSum.KSeries
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

theorem GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ h : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn h (UJset ε) → GlobalTheory.TypeSum.UMG ε h →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε → ‖h y - ∑ a, L a (σ y (w a))‖ < δ) →
    ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
      ∀ y ∈ UJset ε, h y = ∑ a, L a (σ y (w a)) := by
  intro hHC hCW n ε H _ _ _ σ hstd d w hw h hcont humg happ
  obtain ⟨N, Φ, hΦ0, hΦD, hΦG⟩ := humg
  have hCh : CSm ε h := ⟨Φ, hΦ0, hΦD, GlobalTheory.T.continuousOn_rightDerivativeFamily_moderateGrowth n ε N Φ hΦD hΦG⟩
  set h0 : Mx n → ℂ := (UJset ε).indicator h with hh0def
  have hh0 : ∀ g ∈ UJset ε, h g = h0 g := fun g hg => (Set.indicator_of_mem hg h).symm
  have hm0 : h0 ∈ Smo ε := ⟨fun g hg => Set.indicator_of_notMem hg h, hCh.congr hh0⟩
  have hwS : ∀ a, Sm ε σ (w a) := fun a => hstd.2.2.1 _ (hw a)
  have hrel : ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE ltrM (u i) (⟨h0, hm0⟩ : Smo ε) = 0 := by
    intro m c u hcu
    have hA := GlobalTheory.T.rightDerivativeRelation_of_locallyUniformLimit n ε h hCh m c u (fun C hC δ hδ => by
      obtain ⟨L, hL, hLa⟩ := happ C hC δ hδ
      obtain ⟨hB1, hB2⟩ := GlobalTheory.T.coeffSum_smooth_rightDerivWords n ε H σ hstd d L hL w hwS
      refine ⟨_, hB1, hLa, fun y hy => ?_⟩
      simp only [fun i => hB2 (u i) y hy]
      rw [← Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin d))) (f := fun a => L a (σ y (∑ i, c i • wordV σ (u i) (w a))))
        (fun a _ => by rw [hcu a, map_zero, map_zero])]

      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_comm)
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_sum, Submodule.coe_smul, coe_wordE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Submodule.coe_zero, Pi.zero_apply]
    by_cases hg : g ∈ UJset ε
    · rw [← hA g hg]
      exact Finset.sum_congr rfl fun i _ => by rw [wordF_congr hh0 (u i) g hg]
    · refine Finset.sum_eq_zero fun i _ => ?_
      have := (wordE ltrM (u i) (⟨h0, hm0⟩ : Smo ε)).2.1 g hg
      rw [coe_wordE] at this
      rw [this, mul_zero]
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.T.exists_maps_of_relations_alt hHC n ε H σ hstd d w hw (Smo ε) ltrM ⟨h0, hm0⟩ hrel
  have hD : ∀ a, ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε,
      ((Smo ε).subtype ∘ₗ T a) v y = L (σ y v) := by
    intro a
    refine GlobalTheory.T.exists_sobolevContinuous_form_of_moderateGrowthMap hCW n ε H σ hstd N ((Smo ε).subtype ∘ₗ T a) (fun v hv => ?_) (fun v hv k hk g hg => ?_)
      (fun v hv X hX g hg => ?_)
    · obtain ⟨m, c, u, e⟩ := hT3 a v hv
      have hb := fun i => GlobalTheory.T.coeffWord_moderateGrowth_bound n ε N h Φ hΦ0 hΦD hΦG (u i)
      choose C hC using hb
      refine ⟨∑ i, ‖c i‖ * C i, fun g hg => ?_⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, e, Submodule.coe_sum, Submodule.coe_smul, coe_wordE,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, mul_assoc, ← wordF_congr hh0 (u i) g hg]
      exact mul_le_mul_of_nonneg_left (hC i g hg) (norm_nonneg _)
    · have := hT1 a v hv (Sum.inr ⟨k, hk⟩)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [show σ k v = ltrV σ (Sum.inr ⟨k, hk⟩ : Ltr ε) v from rfl, this]
      rfl
    · have := hT1 a v hv (Sum.inl ⟨X, hX⟩)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [show dRep σ X v = ltrV σ (Sum.inl ⟨X, hX⟩ : Ltr ε) v from rfl, this]
      exact (T a v).2.2.hasDerivAt hX hg
  choose L hL1 hL2 using hD
  refine ⟨L, hL1, fun y hy => ?_⟩
  rw [hh0 y hy, show h0 = ((⟨h0, hm0⟩ : Smo ε) : Mx n → ℂ) from rfl, ← hT2, Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => hL2 a (w a) (hw a) y hy
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactAverage_continuousOn_uniformModerateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) ∧
    GlobalTheory.TypeSum.UMG ε (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  first | exact @GlobalTheory.KAvgGrowth.continuousOn_and_umg_kAvg | exact GlobalTheory.KAvgGrowth.continuousOn_and_umg_kAvg | (intros; apply GlobalTheory.KAvgGrowth.continuousOn_and_umg_kAvg <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug.TwistLevels

open Formalism.L2.Host

theorem not_unrAt_mul {L : Type} [Field L] [NumberField L] {d ψ : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (hd : d.UnrAt v) (hψ : ¬ ψ.UnrAt v) : ¬ (d * ψ).UnrAt v := by
  intro h
  apply hψ
  intro x hx
  have := h x hx
  change d.loc v x * ψ.loc v x = 1 at this
  rw [hd x hx, one_mul] at this
  exact this

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {d ψ : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (hd : d.UnrAt v) (hψ : ψ.UnrAt v) : (d * ψ).UnrAt v := by
  intro x hx
  change d.loc v x * ψ.loc v x = 1
  rw [hd x hx, hψ x hx, one_mul]

theorem card_residueField_ne_zero {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) : Nat.card (kP Q) ≠ 0 := by
  have h : Nat.card (kP Q) = Ideal.absNorm Q.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h, Ne, Ideal.absNorm_eq_zero_iff]
  exact Q.ne_bot

def ramSet (P : Pre) (Ξ : Set (HChar P.host.E)) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  {Q | ((P.host.pde * P.host.pde' : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal ∨ ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}

theorem not_unrAt_xiTw (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E))
    (hQ : Q ∈ T.Q w) (hn : ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) : ¬ (T.xiTw f w).UnrAt Q := by
  have h1 : ((B.host.pde : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_right _ h)
  have h2 : ((B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_left _ h)
  have hψ : ¬ (T.psi w).UnrAt Q := fun h => ((T.psi_is w).ram Q).1 h hQ
  unfold TwDat.xiTw
  split_ifs
  · exact not_unrAt_mul (f.isDel'.unr Q h2) hψ
  · exact not_unrAt_mul (f.isDel.unr Q h1) hψ

theorem ram_finite (B : Base) (f : Fr B.toPre) (T : TwDat B) (χ : HChar B.host.E) (hχ : χ ∈ T.set f) :
    {Q : HeightOneSpectrum (𝓞 B.host.E) | ¬ χ.UnrAt Q}.Finite := by
  have hpde : B.host.pde * B.host.pde' ≠ 0 :=
    mul_ne_zero (B.toPre.level_prime _ B.host.pde_level.1).ne_zero (B.toPre.level_prime _ B.host.pde_level.2).ne_zero
  have hZ := GlobalTheory.Mem.Top.TwFin.finite_mem (K := B.host.E) hpde
  have h1 : ∀ Q : HeightOneSpectrum (𝓞 B.host.E), ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal →
      ((B.host.pde : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun Q hn h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_right _ h)
  have h2 : ∀ Q : HeightOneSpectrum (𝓞 B.host.E), ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal →
      ((B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun Q hn h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_left _ h)
  rcases hχ with hχ | ⟨w, rfl⟩
  · rcases hχ with rfl | rfl | rfl
    · exact Set.finite_empty.subset fun Q hQ => hQ fun _ _ => rfl
    · refine hZ.subset fun Q hQ => ?_
      by_contra hn
      exact hQ (f.isDel.unr Q (h1 Q hn))
    · refine hZ.subset fun Q hQ => ?_
      by_contra hn
      exact hQ (f.isDel'.unr Q (h2 Q hn))
  · refine (hZ.union (T.Q w).finite_toSet).subset fun Q hQ => ?_
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hc
    have hψ : (T.psi w).UnrAt Q := ((T.psi_is w).ram Q).2 hc.2
    apply hQ
    unfold TwDat.xiTw
    split_ifs
    · exact unrAt_mul (f.isDel'.unr Q (h2 Q hc.1)) hψ
    · exact unrAt_mul (f.isDel.unr Q (h1 Q hc.1)) hψ


open Classical in
theorem levels_bounded : ∀ (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)), ∃ Ms : Finset ℕ, (∀ M ∈ Ms, M ≠ 0) ∧
    ∀ (B : Base) (hB : B.toPre = P) (T : TwDat B), HEq (T.set (hB ▸ f)) Ξ → ∀ (w : B.places.Pl)
      (S : Finset (HeightOneSpectrum (𝓞 B.host.E))),
      (∀ Q ∈ S, ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal ∨ Q ∈ T.Q w) →
      B.host.g 0 * B.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q ∈ Ms := by
  intro P f Ξ
  by_cases hA : (ramSet P Ξ).Finite
  · refine ⟨hA.toFinset.powerset.image
      (fun S => P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q), ?_, ?_⟩
    · intro M hM
      obtain ⟨S, -, rfl⟩ := Finset.mem_image.1 hM
      refine mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero) ?_
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hq
      exact card_residueField_ne_zero Q
    · intro B hB T hT w S hS
      subst hB
      have hT' : T.set f = Ξ := eq_of_heq hT
      refine Finset.mem_image.2 ⟨S, Finset.mem_powerset.2 fun Q hQ => hA.mem_toFinset.2 ?_, rfl⟩
      rcases hS Q hQ with h | h
      · exact Or.inl h
      · by_cases hn : ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal
        · exact Or.inl hn
        · refine Or.inr ⟨T.xiTw f w, ?_, not_unrAt_xiTw B f T w Q h hn⟩
          rw [← hT']
          exact Set.mem_union_right _ ⟨w, rfl⟩
  · refine ⟨∅, by simp, ?_⟩
    intro B hB T hT w S hS
    subst hB
    exfalso
    apply hA
    have hT' : T.set f = Ξ := eq_of_heq hT
    have hpde : B.host.pde * B.host.pde' ≠ 0 :=
      mul_ne_zero (B.toPre.level_prime _ B.host.pde_level.1).ne_zero (B.toPre.level_prime _ B.host.pde_level.2).ne_zero
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    refine ((GlobalTheory.Mem.Top.TwFin.finite_mem (K := B.host.E) hpde).union
      (hfin.biUnion fun χ hχ => ram_finite B f T χ hχ)).subset ?_
    rintro Q (h | ⟨χ, hχ, hr⟩)
    · exact Or.inl h
    · refine Or.inr (Set.mem_biUnion (x := χ) ?_ hr)
      rw [hT']
      exact hχ

end GlobalTheory.Plug.TwistLevels
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

theorem volPairEx_and_finVol : ∀ (D : D7) (V : HSp D), V.SigOK → VolPairEx V ∧ Formalism.L2.Pj.FinVol V := by
  intro D V hs
  have h := GlobalTheory.Mem.Vol.volIs_trueVol _ _ D.sp.cm _ (tauE D) D.cd V
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hs
  obtain ⟨⟨μ, hμ⟩, hall⟩ := h
  have hex : VolPairEx V := by
    obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hall μ hμ
    exact ⟨(μ, 𝓕), hμ, h𝓕⟩
  refine ⟨hex, ?_⟩
  have hp := volPair_isVolPair V hex
  have hm : (volPair V).1 (volPair V).2 =
      ENNReal.ofReal (GlobalTheory.Mem.Vol.trueVol D.sp.cm (tauE D) D.cd V) :=
    (hall _ hp.1).2 _ hp.2
  unfold Formalism.L2.Pj.FinVol
  rw [muQ_univ, hm]
  exact ⟨(ENNReal.ofReal_pos.2 (GlobalTheory.Mem.Vol.trueVol_pos _ _ _ _)).ne', ENNReal.ofReal_ne_top⟩

end GlobalTheory.FinalJoin2
end
