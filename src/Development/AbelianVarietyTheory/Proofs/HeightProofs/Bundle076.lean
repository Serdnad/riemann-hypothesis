module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle074
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AvgFam

section Compact

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsFiniteMeasure μ]

theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

def intCLM : C(K, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ k, f k ∂μ
      map_add' := fun f g => integral_add (integrable_of_continuous μ f.continuous)
        (integrable_of_continuous μ g.continuous)
      map_smul' := fun c f => integral_smul c _ }
    (μ.real Set.univ) fun f => by
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => f.norm_coe_le_norm k)

theorem continuous_avg {Y : Type} [TopologicalSpace Y] {F : K → Y → ℂ}
    (hF : Continuous fun p : K × Y => F p.1 p.2) : Continuous fun x => ∫ k, F k x ∂μ := by
  let Φ : C(Y × K, ℂ) := ⟨fun p => F p.2 p.1, hF.comp continuous_swap⟩
  exact (intCLM μ).continuous.comp Φ.curry.continuous

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem hasDerivAt_avg (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {F : K → GA D V → ℂ} (hF : ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (hFc : ∀ x, Continuous fun k => F k x)
    (hGc : Continuous fun p : K × GA D V => Rder θ V τ X (F p.1) p.2) (g : GA D V) :
    HasDerivAt (fun t : ℝ => ∫ k, F k (g * oneP θ V τ X t) ∂μ) (∫ k, Rder θ V τ X (F k) g ∂μ) 0 := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hc1 : Continuous fun p : K × ℝ => Rder θ V τ X (F p.1) (g * oneP θ V τ X p.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_const.mul ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).comp continuous_snd)))
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc1.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t k => F k (g * oneP θ V τ X t))
    (F' := fun t k => Rder θ V τ X (F k) (g * oneP θ V τ X t)) (x₀ := 0) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one)
    (Filter.Eventually.of_forall fun t => (hFc _).aestronglyMeasurable)
    (integrable_of_continuous μ (hFc _))
    ((hc1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun k t ht => hC (k, t) ⟨Set.mem_univ _, ht⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ =>
      GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder (hF k) hX) g t)
  have e := key.2
  simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at e
  exact e

end Compact

theorem avg_closed : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  intro D θ hθ V K _ _ _ _ μ _ 𝒢 hc hsm hder
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : ∀ F ∈ 𝒢, ∀ x, Continuous fun k => F k x := fun F hF x =>
    (hc F hF).comp (continuous_id.prodMk continuous_const)
  have hint : ∀ F ∈ 𝒢, ∀ x, Integrable (fun k => F k x) μ := fun F hF x =>
    integrable_of_continuous μ (hk F hF x)
  have hd : ∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, ∀ g, HasDerivAt (fun t : ℝ => ∫ k, F k (g * oneP θ V τ X t) ∂μ)
      (∫ k, Rder θ V τ X (F k) g ∂μ) 0 := fun F hF τ X hX g =>
    hasDerivAt_avg μ hθ hX (hsm F hF) (hk F hF) (hc _ (hder F hF τ X hX)) g
  have hR : ∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ,
      Rder θ V τ X (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, Rder θ V τ X (F k) x ∂μ :=
    fun F hF τ X hX => funext fun g => (hd F hF τ X hX g).deriv
  have hSm : ∀ F ∈ 𝒢, (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := by
    intro F hF
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V {φ | ∃ F ∈ 𝒢, φ = fun x => ∫ k, F k x ∂μ} ?_ ?_ _
      ⟨F, hF, rfl⟩
    · rintro _ ⟨F, hF, rfl⟩
      exact continuous_avg μ (hc F hF)
    · rintro _ ⟨F, hF, rfl⟩ τ X hX
      exact ⟨_, ⟨_, hder F hF τ X hX, rfl⟩, hd F hF τ X hX⟩
  have hW : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ F ∈ 𝒢, (fun k => l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) ∈ 𝒢 ∧
        l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) =
          fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ := by
    intro l hl F hF
    induction l with
    | nil => exact ⟨hF, rfl⟩
    | cons p l ih =>
      obtain ⟨h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      have hp := hl p List.mem_cons_self
      refine ⟨hder _ h1 p.1 p.2 hp, ?_⟩
      simp only [List.foldr_cons]
      rw [h2]
      exact hR _ h1 p.1 p.2 hp
  have hC : ∀ F ∈ 𝒢, ∀ τ Z, (fun k => RderC θ V τ Z (F k)) ∈ 𝒢 ∧
      RderC θ V τ Z (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, RderC θ V τ Z (F k) x ∂μ := by
    intro F hF τ Z
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have m1 := hder F hF τ _ h1
    have m2 := hder F hF τ _ h2
    have e : (fun k => RderC θ V τ Z (F k)) = (fun k => Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) (F k)) +
        Complex.I • (fun k => Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) (F k)) := rfl
    refine ⟨e ▸ add_mem m1 (Submodule.smul_mem _ _ m2), ?_⟩
    have i1 := hint _ m1
    have i2 := hint _ m2
    simp only [RderC]
    rw [hR F hF τ _ h1, hR F hF τ _ h2]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i1 x) ((i2 x).const_mul _), integral_const_mul]
  have hL : ∀ τ (L : List ((GA D V → ℂ) → GA D V → ℂ)), (∀ f ∈ L, ∃ Z, f = RderC θ V τ Z) → ∀ F ∈ 𝒢,
      (fun k => L.foldr (fun f acc => f acc) (F k)) ∈ 𝒢 ∧
        L.foldr (fun f acc => f acc) (fun x => ∫ k, F k x ∂μ) =
          fun x => ∫ k, (L.foldr (fun f acc => f acc) (F k)) x ∂μ := by
    intro τ L hLZ F hF
    induction L with
    | nil => exact ⟨hF, rfl⟩
    | cons f L ih =>
      obtain ⟨h1, h2⟩ := ih fun q hq => hLZ q (List.mem_cons_of_mem _ hq)
      obtain ⟨Z, rfl⟩ := hLZ f List.mem_cons_self
      refine ⟨(hC _ h1 τ Z).1, ?_⟩
      simp only [List.foldr_cons]
      rw [h2]
      exact (hC _ h1 τ Z).2
  intro F hF
  refine ⟨continuous_avg μ (hc F hF), hSm F hF, fun l hl => (hW l hl F hF).2, fun τ j => ?_⟩
  have hmem : ∀ idx : Fin (j + 1) → Fin V.rank, ∀ f ∈ List.ofFn (fun a : Fin (j + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), ∃ Z, f = RderC θ V τ Z := by
    intro idx f hf
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
    exact ⟨_, rfl⟩
  simp only [gelf]
  rw [Finset.sum_congr rfl fun idx _ => (hL τ _ (hmem idx) F hF).2]
  funext x
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ fun idx _ => hint _ (hL τ _ (hmem idx) F hF).1 x]

end GlobalTheory.AvgFam

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CoefRep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem norm_sum_list_le {p : ℕ} (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H) (y : Mx n) :
    ∀ L : List (ℂ × List (Mx n)),
      ‖∑ j, ℓ j (σ y ((L.map fun u => u.1 • Dw σ u.2 (x j)).sum))‖ ≤
        (L.map fun u => ‖u.1‖ * ‖∑ j, ℓ j (σ y (Dw σ u.2 (x j)))‖).sum
  | [] => by simp
  | u :: L => by
    simp only [List.map_cons, List.sum_cons, map_add (f := _), map_smul, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_mul _ _)) (norm_sum_list_le ℓ x y L))

theorem exists_rewrite : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ N : ℕ,
    ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ ∃ (m : List (List (Mx n)) → ℕ) (A : List (List (Mx n)) → ℝ),
    ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) →
    (∀ j, IsKFin ε σ (x j)) → ∀ B : ℕ → ℝ,
    (∀ k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (Dw σ w (x j)))‖ ≤ B k * (1 + hs y) ^ N) →
    ∃ (q : ℕ) (ℓ' : Fin q → (H →ₗ[ℂ] ℂ)) (x' : Fin q → H) (c : Fin q → ℝ),
      (∀ i, Sm ε σ (x' i)) ∧ (∀ i, 0 ≤ c i) ∧ (∀ i w, Sm ε σ w → ‖ℓ' i w‖ ≤ c i * sobNorm σ S w) ∧
      (∀ S', Words (lieSet ε) S' → ∑ i, c i * sobNorm σ S' (x' i) ≤ A S' * B (m S')) ∧
      ∀ y ∈ UJset ε, ∑ j, ℓ j (σ y (x j)) = ∑ i, ℓ' i (σ y (x' i)) := by
  intro _hHC hCW n ε H _ _ _ σ hstd N
  have hσ := hstd.1
  have hcb : CoefBound ε σ := GlobalTheory.TypeSum.coefBound_of_casselmanWallach hCW n ε H σ hstd
  obtain ⟨S, C, hS, hC, hM2⟩ := GlobalTheory.TypeSum.coefBound_two_finSum n ε H σ hstd hcb N
  obtain ⟨d, X, hX, hL1⟩ := GlobalTheory.TypeSum.TraceBound.trace_bound n ε H σ hstd
  have hL1' : ∀ T : List (List (Mx n)), ∃ (r : ℕ) (A : ℝ), Words (lieSet ε) T → ∀ (q : ℕ) (e : Fin q → H)
      (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) →
      (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) → ∑ i, sobNorm σ T (e i) ^ 2 / μ i ^ r ≤ A := by
    intro T
    by_cases hT : Words (lieSet ε) T
    · obtain ⟨r, A, h⟩ := hL1 T hT
      exact ⟨r, A, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hT⟩
  choose r A hrA using hL1'
  have hXl : ∀ i, X i ∈ lieSet ε := fun i => (hX i).1
  refine ⟨S, hS, fun S' => 2 * r (S ++ S'), fun S' => C * (1 + (d : ℝ)) ^ r (S ++ S') * max 0 (A (S ++ S')), ?_⟩
  intro p ℓ x hℓ hx B hB
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    have h := hB k [] (Nat.zero_le _) (by simp) 1 (one_mem_UJ ε)
    have hp : (0 : ℝ) < (1 + hs (1 : Mx n)) ^ N := pow_pos (by linarith [hs_nonneg (1 : Mx n)]) _
    exact (mul_nonneg_iff_of_pos_right hp).1 ((norm_nonneg _).trans h)
  obtain ⟨q, e, μ, he, heK, hμ, heig, hexp⟩ :=
    GlobalTheory.TypeSum.EigenSpan.exists_orthonormal_eigen n ε H σ hstd d X (fun i => ⟨(hX i).1, (hX i).2.1⟩) p x hx
  have heS : ∀ i, Sm ε σ (e i) := fun i => hstd.2.2.1 _ (heK i)
  have hxS : ∀ j, Sm ε σ (x j) := fun j => hstd.2.2.1 _ (hx j)
  have hμ0 : ∀ i (t : ℕ), 0 < μ i ^ t := fun i t => pow_pos (by linarith [hμ i]) t
  have hd0 : (0 : ℝ) ≤ 1 + (d : ℝ) := by positivity
  have key : ∀ (t : ℕ) (i : Fin q) (w : H), Sm ε σ w →
      ‖∑ j, ⟪e i, x j⟫_ℂ * ℓ j w‖ ≤
        C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) * sobNorm σ S w / μ i ^ t := by
    intro t i w hw
    obtain ⟨L, hL1, hL2, hL3⟩ := GlobalTheory.TypeSum.caspow_expand n ε H σ hσ d X hXl t
    have hxt : ∀ j, Sm ε σ ((onePlusCas σ X)^[t] (x j)) := fun j => sm_iterate_onePlusCas hσ hXl (hxS j) t
    have hM : 0 ≤ (1 + (d : ℝ)) ^ t * B (2 * t) := mul_nonneg (pow_nonneg hd0 _) (hB0 _)
    have hgrow : ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y ((onePlusCas σ X)^[t] (x j)))‖ ≤
        (1 + (d : ℝ)) ^ t * B (2 * t) * (1 + hs y) ^ N := by
      intro y hy
      have e1 : ∀ j, (onePlusCas σ X)^[t] (x j) = (L.map fun u => u.1 • Dw σ u.2 (x j)).sum :=
        fun j => hL3 _ (hxS j)
      simp only [e1]
      refine (norm_sum_list_le ℓ x y L).trans ?_
      have hw0 : 0 ≤ B (2 * t) * (1 + hs y) ^ N :=
        mul_nonneg (hB0 _) (pow_nonneg (by linarith [hs_nonneg y]) _)
      calc (L.map fun u => ‖u.1‖ * ‖∑ j, ℓ j (σ y (Dw σ u.2 (x j)))‖).sum
          ≤ (L.map fun u => ‖u.1‖ * (B (2 * t) * (1 + hs y) ^ N)).sum := by
            refine List.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine hB (2 * t) u.2 (hL1 u hu).1 (fun Y hY => ?_) y hy
            obtain ⟨i, rfl⟩ := (hL1 u hu).2 Y hY
            exact hX i
        _ = (L.map fun u => ‖u.1‖).sum * (B (2 * t) * (1 + hs y) ^ N) := List.sum_map_mul_right _ _ _
        _ ≤ (1 + (d : ℝ)) ^ t * (B (2 * t) * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_right hL2 hw0
        _ = _ := by ring
    have h2 := hM2 p ℓ _ hℓ hxt _ hM hgrow (e i) w (heS i) hw
    have e2 : ∀ j, ⟪e i, (onePlusCas σ X)^[t] (x j)⟫_ℂ = ((μ i : ℂ) ^ t) * ⟪e i, x j⟫_ℂ := fun j => by
      rw [inner_iterate_onePlusCas hσ hXl (heS i) (hxS j),
        iterate_onePlusCas_of_eq hσ hXl (heS i) (heig i), inner_smul_left]
      congr 1
      rw [← Complex.ofReal_pow, Complex.conj_ofReal]
    simp only [e2, mul_assoc, ← Finset.mul_sum] at h2
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith [hμ i])] at h2
    rw [le_div_iff₀ (hμ0 i t)]
    have hc := mul_comm (‖∑ j, ⟪e i, x j⟫_ℂ * ℓ j w‖) (μ i ^ t)
    linarith
  have hterm : ∀ (i : Fin q) (t : ℕ), 0 ≤ C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t :=
    fun i t => div_nonneg (mul_nonneg (mul_nonneg hC (mul_nonneg (pow_nonneg hd0 _) (hB0 _)))
      (sobNorm_nonneg σ S _)) (hμ0 i t).le
  have hbdd : ∀ i : Fin q, BddBelow (Set.range fun t : ℕ =>
      C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t) :=
    fun i => ⟨0, by rintro _ ⟨t, rfl⟩; exact hterm i t⟩
  refine ⟨q, fun i => ∑ j, ⟪e i, x j⟫_ℂ • ℓ j, e,
    fun i => ⨅ t : ℕ, C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t,
    heS, fun i => le_ciInf fun t => hterm i t, ?_, ?_, ?_⟩
  · intro i w hw
    have e3 : (∑ j, ⟪e i, x j⟫_ℂ • ℓ j) w = ∑ j, ⟪e i, x j⟫_ℂ * ℓ j w := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e3, mul_comm, Real.mul_iInf_of_nonneg (sobNorm_nonneg σ S w)]
    refine le_ciInf fun t => (key t i w hw).trans (le_of_eq ?_)
    ring
  · intro S' hS'
    have hW : Words (lieSet ε) (S ++ S') := words_append hS hS'
    have hA := hrA (S ++ S') hW q e μ he heK hμ heig
    set r₀ := r (S ++ S')
    have hK0 : 0 ≤ C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) :=
      mul_nonneg hC (mul_nonneg (pow_nonneg hd0 _) (hB0 _))
    calc ∑ i, (⨅ t : ℕ, C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t) * sobNorm σ S' (e i)
        ≤ ∑ i, C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * sobNorm σ S (e i) / μ i ^ r₀ * sobNorm σ S' (e i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ciInf_le (hbdd i) r₀) (sobNorm_nonneg σ S' _)
      _ ≤ ∑ i, C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * (sobNorm σ (S ++ S') (e i) ^ 2 / μ i ^ r₀) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have a0 := sobNorm_nonneg σ S (e i)
          have b0 := sobNorm_nonneg σ S' (e i)
          have hab : sobNorm σ S (e i) * sobNorm σ S' (e i) ≤ sobNorm σ (S ++ S') (e i) ^ 2 := by
            rw [sobNorm_append]; nlinarith
          have hm := hμ0 i r₀
          calc C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * sobNorm σ S (e i) / μ i ^ r₀ * sobNorm σ S' (e i)
              = C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * (sobNorm σ S (e i) * sobNorm σ S' (e i) / μ i ^ r₀) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hab hm.le) hK0
      _ = C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * ∑ i, sobNorm σ (S ++ S') (e i) ^ 2 / μ i ^ r₀ := by
          rw [Finset.mul_sum]
      _ ≤ C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * max 0 (A (S ++ S')) :=
          mul_le_mul_of_nonneg_left (hA.trans (le_max_right _ _)) hK0
      _ = C * (1 + (d : ℝ)) ^ r (S ++ S') * max 0 (A (S ++ S')) * B (2 * r (S ++ S')) := by ring
  · intro y _
    have h1 : ∀ j, ℓ j (σ y (x j)) = ∑ i, ⟪e i, x j⟫_ℂ * ℓ j (σ y (e i)) := fun j => by
      conv_lhs => rw [hexp j]

      simp only [map_sum, map_smul, smul_eq_mul]
    simp only [h1, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_comm

end GlobalTheory.TypeSum.CoefRep

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.exists_sobolevContinuous_form_of_moderateGrowthMap : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (N : ℕ) (T : H →ₗ[ℂ] (Mx n → ℂ)),
    (∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N) →
    (∀ v, IsKFin ε σ v → ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, T (σ k v) g = T v (g * k)) →
    (∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0) →
    ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, T v y = L (σ y v) := by
  first | exact @GlobalTheory.TypeSum.GrowthForm.exists_form | exact GlobalTheory.TypeSum.GrowthForm.exists_form | (intros; apply GlobalTheory.TypeSum.GrowthForm.exists_form <;> assumption)
end
