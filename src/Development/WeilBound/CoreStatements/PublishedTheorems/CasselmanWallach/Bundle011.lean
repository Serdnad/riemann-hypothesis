module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle183
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.NilpotentOfPowerTraces
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
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
public import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA

@[expose] public section

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW

namespace HilbertSchmidtSqEq₂

theorem hs2_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs2 g = hs g := rfl

theorem smul_seminorm_cont {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {q : Seminorm ℂ E}
    (hq : Continuous q) (c : NNReal) : Continuous (c • q) := by
  rw [Seminorm.coe_smul]
  exact hq.const_smul c

end HilbertSchmidtSqEq₂

open HilbertSchmidtSqEq₂ in
theorem e3c : SmoothMapSeminormBound := by
  classical
  intro hM e3a e3b n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD A hA hMod T hG hd Q N hQc hQg hη
  obtain ⟨m, K, I₀, hK, hmax⟩ := hM n ε (kfin ε σ) A hMod N
  have hC : ∀ e : kfin ε σ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, Sm ε σ y → ‖⟪(e : H), y⟫_ℂ‖ ≤ C * Q (T y) :=
    fun e => hη e e.2
  choose Ce hCe0 hCe using hC
  set Cs : ℝ := ∑ e ∈ I₀, Ce e with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun e _ => hCe0 e
  have h3a := e3a n ε (kfin ε σ) A hMod.gl hMod.uni hMod m
  obtain ⟨D, hDm⟩ := e3b n ε H σ hU hI E p π dπ hπ A hA T hd m
  have key : ∀ y : kfin ε σ, ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) := by
    intro y
    obtain ⟨v, hv⟩ := h3a.1 y
    set w : H := ((((1 + casimirK ε A) ^ m) y : kfin ε σ) : H) with hwdef
    have hw : Sm ε σ w := hD.1 _ (((1 + casimirK ε A) ^ m) y).2
    let F : kfin ε σ →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
      { toFun := fun η g => ⟪w, σ g (η : H)⟫_ℂ
        map_add' := fun a b => by funext g; simp [inner_add_right]
        map_smul' := fun c a => by funext g; simp [inner_smul_right] }
    have hF : ∀ (η : kfin ε σ) g, F η g = ⟪w, σ g (η : H)⟫_ℂ := fun _ _ => rfl
    have h1 : ∀ η : kfin ε σ, ContinuousOn (F η) (ReciprocityTheory.ChartRestriction.DS.UJset ε) := fun η => by
      have := (continuousOn_const (c := w) (s := UJset ε)).inner (𝕜 := ℂ) (hU.2.2 (η : H))
      exact this
    have h2 : ∀ X, ReciprocityTheory.ChartRestriction.DS.inP ε X → ∀ η : kfin ε σ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε,
        HasDerivAt (fun t : ℝ => F η (g * NormedSpace.exp (t • X))) (F (actM A X η) g) 0 := by
      intro X hX η g hg
      have hXl : X ∈ lieSet ε := hX.1
      have hg' : g ∈ UJset ε := hg
      have hη' : Sm ε σ (η : H) := hD.1 _ η.2
      have ho : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (η : H)) (dRep σ X η) 0 := by
        have := hasDerivAt_orbit hU hη' hXl 0
        rwa [zero_smul, NormedSpace.exp_zero, sigma_one hU] at this
      have h4 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp (t • X)) (η : H))) (σ g (dRep σ X η)) 0 :=
        ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 ho
      have h5 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h4
      simp only [ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at h5
      rw [hF, hA X hXl η]
      refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, hF, innerSL_apply_apply]
      rw [sigma_mul hU hg' (exp_mem_UJ hXl t)]
    have h3 : ∀ η : kfin ε σ, ∃ C : ℝ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F η g‖ ≤ C * (1 + hs2 g) ^ N := by
      intro η
      refine ⟨‖w‖ * ‖(η : H)‖, fun g hg => ?_⟩
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq]
      have e1 : ‖⟪w, σ g (η : H)⟫_ℂ‖ ≤ ‖w‖ * ‖(η : H)‖ := by
        have := norm_inner_le_norm (𝕜 := ℂ) w (σ g (η : H))
        rwa [hU.2.1 g hg' (η : H)] at this
      have e2 : (1 : ℝ) ≤ (1 + hs g) ^ N := one_le_pow₀ (by linarith [hs_nonneg g])
      calc _ ≤ ‖w‖ * ‖(η : H)‖ := e1
        _ = ‖w‖ * ‖(η : H)‖ * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
    have h5b : ∀ e ∈ I₀, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F e g‖ ≤ (Cs * Q (T w)) * (1 + hs2 g) ^ N := by
      intro e he g hg
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq, inner_sigma hU hg' w (e : H), norm_inner_symm]
      have hgi : g⁻¹ ∈ UJset ε := inv_mem_UJ hg'
      have e1 := hCe e (σ g⁻¹ w) (Sm.translate hU hw hgi)
      rw [hG.1 g⁻¹ hgi w hw] at e1
      have e2 := hQg g⁻¹ hgi (T w)
      rw [hs_inv hg'] at e2
      have e3 : Ce e ≤ Cs := Finset.single_le_sum (f := Ce) (fun x _ => hCe0 x) he
      have hQ0 : 0 ≤ Q (T w) := apply_nonneg _ _
      have hW0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
      calc _ ≤ Ce e * Q (π g⁻¹ (T w)) := e1
        _ ≤ Ce e * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_left e2 (hCe0 e)
        _ ≤ Cs * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_right e3 (mul_nonneg hW0 hQ0)
        _ = _ := by ring
    have hmv := hmax F h1 h2 h3 (Cs * Q (T w)) (mul_nonneg hCs0 (apply_nonneg _ _)) h5b v
    rw [hv, hF, sigma_one hU] at hmv
    have hin : ⟪w, (v : H)⟫_ℂ = ⟪(y : H), (y : H)⟫_ℂ := by
      rw [hwdef, ← Submodule.coe_inner, ← Submodule.coe_inner, h3a.2 y v, hv]
    have hn : ‖⟪(y : H), (y : H)⟫_ℂ‖ = ‖(y : H)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow]; simp
    rw [hin, hn] at hmv
    have hTw : T w = D (T y) := hDm y
    rw [hTw] at hmv
    have hy0 : 0 ≤ ‖(y : H)‖ := norm_nonneg _
    have hR0 : 0 ≤ K * Cs * Q (D (T y)) := mul_nonneg (mul_nonneg hK hCs0) (apply_nonneg _ _)
    rcases hy0.eq_or_lt with h0 | h0
    · rw [← h0]; exact hR0
    · have : ‖(y : H)‖ * ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) * ‖(y : H)‖ := by
        have e : K * (Cs * Q (D (T y))) * ‖(y : H)‖ = K * Cs * Q (D (T y)) * ‖(y : H)‖ := by ring
        rw [← e, ← sq]
        exact hmv
      exact le_of_mul_le_mul_right this h0
  refine ⟨(K * Cs).toNNReal • Q.comp (D : E →ₗ[ℂ] E), smul_seminorm_cont ?_ _, fun v hv => ?_⟩
  · rw [Seminorm.coe_comp]
    exact hQc.comp D.continuous
  · rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (mul_nonneg hK hCs0),
      Seminorm.comp_apply]
    exact key ⟨v, hv⟩

end PositivityTheory.CW

end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKHWVec IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.HighestWeightKernel

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem inner_compact (hU : IsInfUnitary ε E) {a b : Fin n} (h : ε a = ε b) (x y : V) :
    ⟪E b a x, y⟫_ℂ = ⟪x, E a b y⟫_ℂ := by
  have := hU b a x y
  simpa [adjSign, h.symm] using this

theorem exists_hull (hL : LocFin ε E) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ IsKStableSub ε E Y ∧ W ≤ Y := by
  classical
  choose S hSfin hSmem hSk using hL
  let bW := Module.finBasis ℂ W
  let Y : Submodule ℂ V := ⨆ i, S (bW i : V)
  haveI : ∀ i, FiniteDimensional ℂ (S (bW i : V)) := fun i => hSfin _
  refine ⟨Y, Submodule.finite_iSup _, ?_, ?_⟩
  · intro a b hab v hv
    refine Submodule.iSup_induction (fun i => S (bW i : V)) (motive := fun x => E a b x ∈ Y) hv ?_ ?_ ?_
    · intro i x hx
      exact (le_iSup (fun i => S (bW i : V)) i) (hSk _ a b hab x hx)
    · simp
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
  · intro w hw
    have hrep := bW.sum_repr ⟨w, hw⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V) := by
      have := congrArg Subtype.val hrep
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hw']
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    exact (le_iSup (fun i => S (bW i : V)) i) (hSmem _)

theorem inner_casimirK (hU : IsInfUnitary ε E) (w : V) :
    ⟪w, casimirK ε E w⟫_ℂ =
      ((∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b hb => ?_))
  have hba : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [← inner_compact hU hba.symm, inner_self_eq_norm_sq_to_K]
  first
    | rfl
    | simp
    | norm_cast

theorem mem_ker_iff (μ : ℝ) (x : V) :
    x ∈ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V)) ↔ casimirK ε E x = (μ : ℂ) • x := by
  simp [LinearMap.mem_ker, sub_eq_zero]

theorem sq_le_of_khw (hU : IsInfUnitary ε E) {w : V} (hw0 : w ≠ 0) {μ : ℝ} (hwμ : casimirK ε E w = (μ : ℂ) • w)
    {Λ : Fin n → ℝ} (hkw : IsKHWVec ε E Λ w) : (∑ a, Λ a ^ 2) ≤ μ := by
  have h1 := inner_casimirK hU w
  rw [hwμ, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  have h2 : μ * ‖w‖ ^ 2 = ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    exact h1
  have h3 : ∑ a, Λ a ^ 2 * ‖w‖ ^ 2 ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hmem : a ∈ Finset.univ.filter (fun b => ε b = ε a) := by simp
    have hle := Finset.single_le_sum (f := fun b => ‖E b a w‖ ^ 2) (fun b _ => by positivity) hmem
    have hEa : ‖E a a w‖ ^ 2 = Λ a ^ 2 * ‖w‖ ^ 2 := by
      rw [hkw.1 a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    linarith
  have hpos : 0 < ‖w‖ ^ 2 := by positivity
  rw [← Finset.sum_mul] at h3
  nlinarith

theorem mem_of_eig (hgl : IsGlRep E) (hU : IsInfUnitary ε E) (hL : LocFin ε E)
    (h3 : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → IsKStableSub ε E S → S ≠ ⊥ →
      ∃ (w : V) (μ : Fin n → ℝ), w ∈ S ∧ w ≠ 0 ∧ IsKHWVec ε E μ w)
    (hint : ∀ (v : V) (a : Fin n) (x : ℝ), v ≠ 0 → E a a v = (x : ℂ) • v → ∃ z : ℤ, x = z)
    {Y : Submodule ℂ V} (hYk : IsKStableSub ε E Y) {μ : ℝ}
    (hY : ∀ (w : V) (Λ : Fin n → ℤ), IsKHWVec ε E (fun a => ((Λ a : ℤ) : ℝ)) w →
      (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ μ → w ∈ Y)
    {v : V} (hv : Eig ε E μ v) : v ∈ Y := by
  classical
  have key : ∀ k : ℕ, ∀ Z : Submodule ℂ V, FiniteDimensional ℂ Z → Module.finrank ℂ Z = k →
      IsKStableSub ε E Z → (∀ z ∈ Z, casimirK ε E z = (μ : ℂ) • z) → Z ≤ Y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Z hZf hZk hZs hZc
      by_cases hZ0 : Z = ⊥
      · rw [hZ0]
        exact bot_le
      obtain ⟨w, Λ, hwZ, hw0, hkw⟩ := h3 Z hZf hZs hZ0
      have hΛ : ∀ a, ∃ z : ℤ, Λ a = z := fun a => hint w a (Λ a) hw0 (hkw.1 a)
      choose Λz hΛz using hΛ
      have hkw' : IsKHWVec ε E (fun a => ((Λz a : ℤ) : ℝ)) w := by
        have : Λ = fun a => ((Λz a : ℤ) : ℝ) := funext hΛz
        rw [← this]
        exact hkw
      have hsq : (∑ a, ((Λz a : ℤ) : ℝ) ^ 2) ≤ μ := sq_le_of_khw hU hw0 (hZc w hwZ) hkw'
      have hwY : w ∈ Y := hY w Λz hkw' hsq
      let Kw : Submodule ℂ V := sInf {T | w ∈ T ∧ IsKStableSub ε E T}
      have hKwS : IsKStableSub ε E Kw := by
        intro a b hab x hx
        rw [Submodule.mem_sInf] at hx ⊢
        intro T hT
        exact hT.2 a b hab x (hx T hT)
      have hwKw : w ∈ Kw := Submodule.mem_sInf.2 (fun T hT => hT.1)
      have hKwZ : Kw ≤ Z := sInf_le ⟨hwZ, hZs⟩
      have hKwY : Kw ≤ Y := sInf_le ⟨hwY, hYk⟩
      haveI : FiniteDimensional ℂ Kw := Submodule.finiteDimensional_of_le hKwZ
      have hZ'lt : Kwᗮ ⊓ Z < Z := by
        refine lt_of_le_of_ne inf_le_right (fun h => ?_)
        have hwZ' : w ∈ Kwᗮ ⊓ Z := by
          rw [h]
          exact hwZ
        have h0 : ⟪w, w⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hwKw hwZ'.1
        exact hw0 (inner_self_eq_zero.1 h0)
      haveI : FiniteDimensional ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hZ'k : IsKStableSub ε E (Kwᗮ ⊓ Z) := by
        intro a b hab x hx
        refine ⟨?_, hZs a b hab x hx.2⟩
        show E a b x ∈ Kwᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        rw [← inner_compact hU hab]
        exact Submodule.inner_right_of_mem_orthogonal (hKwS b a hab.symm u hu) hx.1
      have hlt : Module.finrank ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) < k :=
        hZk ▸ Submodule.finrank_lt_finrank_of_lt hZ'lt
      have hZ'le : Kwᗮ ⊓ Z ≤ Y :=
        ih _ hlt _ inferInstance rfl hZ'k (fun z hz => hZc z hz.2)
      have hsplit : Kw ⊔ Kwᗮ ⊓ Z = Z :=
        Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKwZ
      rw [← hsplit]
      exact sup_le hKwY hZ'le
  obtain ⟨S, hSf, hvS, hSk⟩ := hL v
  haveI : FiniteDimensional ℂ S := hSf
  let Z : Submodule ℂ V := S ⊓ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V))
  have hZk : IsKStableSub ε E Z := by
    intro a b hab x hx
    refine ⟨hSk a b hab x hx.1, ?_⟩
    have hx2 := (mem_ker_iff μ x).1 hx.2
    refine (mem_ker_iff μ _).2 ?_
    have hc := ReciprocityTheory.ChartRestriction.DS.casimirK_comm ε hgl a b hab
    have := congrArg (fun U : Module.End ℂ V => U x) hc
    simp only [Module.End.mul_apply] at this
    rw [this, hx2, map_smul]
  exact key _ Z (Submodule.finiteDimensional_of_le inf_le_left) rfl hZk
    (fun z hz => (mem_ker_iff μ z).1 hz.2) ⟨hvS, (mem_ker_iff μ v).2 hv⟩

end PositivityTheory.CW.HighestWeightKernel

namespace PositivityTheory.CW

open PositivityTheory.CW.HighestWeightKernel

theorem k_types_finite_of_highest_weight (h : KStableHighestWeightVector) : KTypesBoundedFinite := by
  classical
  intro n ε V _ _ E hgl hU hL hfinHW hint R
  let F : Set (Fin n → ℤ) := {Λ | (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ R}
  have hFfin : F.Finite := by
    refine (Set.Finite.pi (t := fun _ => Set.Icc (-⌈R⌉) ⌈R⌉) (fun _ => Set.finite_Icc _ _)).subset ?_
    intro Λ hΛ a _
    have hsq : ((Λ a : ℤ) : ℝ) ^ 2 ≤ R := by
      refine le_trans ?_ hΛ
      exact Finset.single_le_sum (f := fun b => ((Λ b : ℤ) : ℝ) ^ 2) (fun b _ => by positivity)
        (Finset.mem_univ a)
    have h1 : ((Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by exact_mod_cast Int.le_self_sq (Λ a)
    have h2 : (-(Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by
      have := Int.le_self_sq (-(Λ a))
      rw [neg_sq] at this
      exact_mod_cast this
    have hc := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉ : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : ((Λ a : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  haveI : Finite F := hFfin.to_subtype
  let W0 : Submodule ℂ V :=
    ⨆ Λ : F, Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}
  haveI : ∀ Λ : F, FiniteDimensional ℂ
      (Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) := fun Λ => hfinHW _
  haveI : FiniteDimensional ℂ W0 := Submodule.finite_iSup _
  obtain ⟨Y, hYf, hYk, hWY⟩ := exists_hull hL W0
  haveI : FiniteDimensional ℂ Y := hYf
  refine Submodule.finiteDimensional_of_le (S₂ := Y) ?_
  refine Submodule.span_le.2 ?_
  rintro v ⟨μ, hμR, hv⟩
  refine mem_of_eig hgl hU hL (h n ε V E hgl hU) hint hYk (μ := μ) ?_ hv
  intro w Λ hkw hsq
  have hΛF : Λ ∈ F := le_trans hsq hμR
  exact hWY ((le_iSup (fun Λ : F => Submodule.span ℂ
    {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) ⟨Λ, hΛF⟩) (Submodule.subset_span hkw))

end PositivityTheory.CW

end
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW

namespace DerivativeContinuity

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem continuousOn_Dw (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    ContinuousOn (fun g => Dw σ l (σ g w)) (UJset ε) :=
  continuousOn_iff_continuous_restrict.2
    (continuous_word_orbit (isUnit_Jm ε) hU (GlobalTheory.CWGeneral.dense_smoothAll_of_irred hU hI) continuous_subtype_val
      (fun t => t.2) l hl hw)

theorem hasDerivAt_Dw (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) {X : Mx n} (hX : X ∈ lieSet ε) :
    HasDerivAt (fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) w)) (Dw σ l (dRep σ X w)) 0 := by
  have hden : Dense (smooth (Jm ε) σ : Set H) :=
    (GlobalTheory.CWGeneral.dense_smoothAll_of_irred hU hI).mono (smoothAll_le (isUnit_Jm ε))
  have hw' : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) hU hw hX
  have hc : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) →
      Continuous fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) (dRep σ X w)) := fun l hl =>
    (continuousOn_Dw hU hI hl hw').comp_continuous (continuous_exp_smul X) (exp_mem_UJ hX)
  have e0 : ∀ z, σ (NormedSpace.exp ((0 : ℝ) • X)) z = z := fun z => by
    rw [zero_smul, NormedSpace.exp_zero, sigma_one hU]
  have key : ∀ t : ℝ, Dw σ l (σ (NormedSpace.exp (t • X)) w) =
      Dw σ l w + ∫ s in (0 : ℝ)..t, Dw σ l (σ (NormedSpace.exp (s • X)) (dRep σ X w)) := by
    intro t
    have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun s _ => hasDerivAt_orbit hU hw hX s) ((hc [] (by simp)).intervalIntegrable 0 t)
    rw [e0] at h0
    refine hden.eq_of_inner_right ℂ fun y hy => ?_
    have i1 := fun (z : H) (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) =>
      (innerSL ℂ z).intervalIntegral_comp_comm ((hc l hl).intervalIntegrable (μ := volume) 0 t)
    simp only [innerSL_apply_apply] at i1
    have i2 := i1 (Dw σ l.reverse y) [] (by simp)
    simp only [Dw, List.foldr_nil] at i2
    rw [inner_add_right, ← i1 y l hl, inner_Dw hU hl hy (hw.translate hU (exp_mem_UJ hX t)), inner_Dw hU hl hy hw]
    simp only [fun s => inner_Dw hU hl hy (hw'.translate hU (exp_mem_UJ hX s))]
    rw [intervalIntegral.integral_const_mul, i2, h0, inner_sub_right]
    ring
  simp only [key]
  have := ((hc l hl).integral_hasStrictDerivAt 0 0).hasDerivAt.const_add (Dw σ l w)
  rwa [e0] at this

end DerivativeContinuity

theorem c6 : C6 := fun _ _ _ _ _ _ _ hU hI _ hl _ hw _ hX => DerivativeContinuity.hasDerivAt_Dw hU hI hl hw hX

end PositivityTheory.CW
end

section

open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW.DerivativeRepresentation

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_eq_dRep (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : ReciprocityTheory.ChartRestriction.DS.dS σ X w = dRep σ X w := by
  unfold ReciprocityTheory.ChartRestriction.DS.dS dRep
  simp only [Complex.coe_smul]

theorem bridge (hσ : IsURepOn (UJset ε) σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)} (hE : PositivityTheory.CW.KDer ε σ E)
    (v : kfin ε σ) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) (a b : Fin n) :
    ((E a b v : kfin ε σ) : H) = ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) := by
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ]
  set Z : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  have h1 := ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε Z
  have h2 := ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε Z
  have hd : E a b = ReciprocityTheory.ChartRestriction.DS.actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε Z) +
      Complex.I • ReciprocityTheory.ChartRestriction.DS.actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε Z) := by
    rw [← ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_smul, ← ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_add,
      ← ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp, ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_single]
  rw [hd, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hE _ h1 v, hE _ h2 v, dS_eq_dRep, dS_eq_dRep]

end PositivityTheory.CW.DerivativeRepresentation

namespace PositivityTheory.CW

open DerivativeRepresentation in
theorem c2a : CardSubmodulesOfIndexLePow := by
  intro n ε H _ _ _ σ hσ hirr E hE v
  have hsm := (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1
  obtain ⟨S0, hS0f, hvS0, hS0K⟩ := v.2
  have hS0k : ∀ x ∈ S0, IsKFin ε σ x := fun x hx => ⟨S0, hS0f, hx, hS0K⟩
  let S : Submodule ℂ (kfin ε σ) := S0.comap (kfin ε σ).subtype
  let f : S →ₗ[ℂ] S0 :=
    { toFun := fun x => ⟨((x : kfin ε σ) : H), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y h => by
    apply Subtype.ext; apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  refine ⟨S, Module.Finite.of_injective f hf, hvS0, fun a b hab w hw => ?_⟩
  show ((E a b w : kfin ε σ) : H) ∈ S0
  rw [bridge hσ hE w (hsm _ w.2)]
  exact CompanionTheory.D.gk.HC.smE_mem_of_compact_A hσ hS0K hab _ hw

end PositivityTheory.CW
end
