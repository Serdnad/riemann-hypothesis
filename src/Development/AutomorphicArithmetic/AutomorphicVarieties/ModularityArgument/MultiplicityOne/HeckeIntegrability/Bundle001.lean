module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

namespace UpperTheory.V.Z.Mult.Pi

private lemma trace_idem {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (f : Module.End ℂ Y) (hf : f * f = f) (hx : ∀ x, ∃ c : ℂ, f * x * f = c • f) (h0 : f ≠ 0) :
    LinearMap.trace ℂ Y f = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (LinearMap.ext h)
  have hidem : ∀ v, f (f v) = f v := fun v => by
    have := congrArg (fun g : Module.End ℂ Y => g v) hf
    simpa [Module.End.mul_apply] using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ (f y) = 1 := by
    have h1 : ¬ ∀ φ : Module.Dual ℂ Y, φ (f y) = 0 := fun h =>
      hy ((Module.forall_dual_apply_eq_zero_iff ℂ (f y)).1 h)
    push_neg at h1
    obtain ⟨ψ, hψ⟩ := h1
    refine ⟨(ψ (f y))⁻¹ • ψ, ?_⟩
    simp [hψ]
  have hr : LinearMap.range f = Submodule.span ℂ {f y} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨c, hc⟩ := hx (φ.smulRight v)
      have h2 := congrArg (fun g : Module.End ℂ Y => g (f y)) hc
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, hidem, hφ,
        map_smul, one_smul] at h2
      exact Submodule.mem_span_singleton.2 ⟨c, h2.symm⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨y, rfl⟩
  have hp : LinearMap.IsProj (LinearMap.range f) f :=
    ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hidem v⟩
  rw [hp.trace, hr, finrank_span_singleton hy]
  simp

theorem rankOne_pf : RankOne := by
  intro Y _ _ _ f A hf hA hc hx
  by_cases h0 : f = 0
  · left
    simp [h0]
  right
  obtain ⟨c, hcA⟩ := hx A
  have hfA : f * A = c • f := by
    calc f * A = f * f * A := by rw [hf]
      _ = f * (f * A) := mul_assoc _ _ _
      _ = f * (A * f) := by rw [hc]
      _ = f * A * f := (mul_assoc _ _ _).symm
      _ = c • f := hcA
  have hsq : (c * c) • f = f := by
    calc (c * c) • f = (c • f) * (c • f) := by rw [smul_mul_smul_comm, hf]
      _ = (f * A) * (f * A) := by rw [hfA]
      _ = f * (A * f) * A := by simp only [mul_assoc]
      _ = f * (f * A) * A := by rw [hc]
      _ = (f * f) * (A * A) := by simp only [mul_assoc]
      _ = f := by rw [hf, hA, mul_one]
  have hcc : c * c = 1 := by
    have h3 : (c * c - 1) • f = 0 := by rw [sub_smul, one_smul, hsq, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h0
  have hn : ‖c‖ = 1 := by
    have h4 : ‖c‖ * ‖c‖ = 1 := by rw [← norm_mul, hcc, norm_one]
    nlinarith [norm_nonneg c, sq_nonneg (‖c‖ - 1)]
  rw [hfA, map_smul, trace_idem f hf hx h0, smul_eq_mul, mul_one, hn]

end UpperTheory.V.Z.Mult.Pi
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F
open PositivityTheory.RgTw (Mat G)

private theorem hecke_comp {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {φ : G → G} (hc : Continuous φ)
    (hi : ∀ g, φ (φ g) = g) (hm : ∀ a b, φ (a * b) = φ a * φ b) (hK : ∀ k ∈ K, φ k ∈ K) {h : G → ℂ}
    (hh : IsHecke K h) : IsHecke K (fun g => h (φ g)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · let e : G ≃ₜ G :=
      { toFun := φ, invFun := φ, left_inv := hi, right_inv := hi,
        continuous_toFun := hc, continuous_invFun := hc }
    exact hh.1.comp_homeomorph e
  · simp only [hm]
    exact hh.2 _ (hK k hk) _

private theorem core {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (hS : LvShift) (ρ : Representation ℂ G V) (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (u : G) (hu : ∀ x, x ∈ K ↔ u * x * u⁻¹ ∈ K) (θ : G → G)
    (hθc : Continuous θ) (hθi : ∀ g, θ (θ g) = g) (hθm : ∀ a b, θ (a * b) = θ a * θ b) (hθK : ∀ k ∈ K, θ k ∈ K)
    (hθu : θ u = u⁻¹) (Y : Submodule ℂ V) (hY : Y ≤ fixed ρ K) (r : (G → ℂ) → Module.End ℂ Y)
    (hact : ∀ h, IsHecke K h → ∀ y : Y, (r h y : V) = Lv ρ K h y)
    (A : Module.End ℂ Y) (hAA : A * A = 1)
    (hA : ∀ h, IsHecke K h → A * r h = r (fun g => h (θ g)) * A) :
    (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) = 1 ∧
    (∀ h, IsHecke K h → (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * r h =
      r (fun g => h (u * θ g * u⁻¹)) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A)) ∧
    ∀ h, IsHecke K h → IsHecke K (fun g => h (g * u⁻¹)) ∧
      r (fun g => h (g * u⁻¹)) = r h * r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) := by
  have h0 : IsHecke K (0 : G → ℂ) := ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have Sh := hS G V ρ K ho hc
  have hI : IsHecke K ((K : Set G).indicator 1) := (Sh u hu 0 h0).2.2.1
  have hu' : ∀ x, x ∈ K ↔ u⁻¹ * x * u⁻¹⁻¹ ∈ K := fun x => by
    rw [hu (u⁻¹ * x * u⁻¹⁻¹)]
    simp [mul_assoc]

  have a1 : ∀ v : G, (∀ x, x ∈ K ↔ v * x * v⁻¹ ∈ K) → ∀ y : Y,
      (r (fun g => (K : Set G).indicator 1 (v⁻¹ * g)) y : V) = ρ v y := fun v hv y => by
    obtain ⟨-, hl, -, -⟩ := Sh v hv _ hI
    obtain ⟨-, -, e1, e2⟩ := (Sh v hv _ hI).2.2.2 y (hY y.2)
    rw [hact _ hl, e1, e2]
  set Ru := r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) with hRu
  set Ru' := r (fun g => (K : Set G).indicator 1 (u * g)) with hRu'
  have b1 : ∀ y : Y, (Ru y : V) = ρ u y := a1 u hu
  have b2 : ∀ y : Y, (Ru' y : V) = ρ u⁻¹ y := fun y => by
    have := a1 u⁻¹ hu' y
    simpa only [inv_inv] using this
  have hRR : Ru * Ru' = 1 := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    show (Ru (Ru' y) : V) = y
    rw [b1, b2, ← Module.End.mul_apply, ← map_mul]
    simp
  have hAR : A * Ru = Ru' * A := by
    rw [hRu, hA _ (Sh u hu _ hI).2.1, hRu']
    congr 2
    funext g
    have e : u⁻¹ * θ g = θ (u * g) := by rw [hθm, hθu]
    have m : θ (u * g) ∈ K ↔ u * g ∈ K :=
      ⟨fun h => by simpa only [hθi] using hθK _ h, hθK _⟩
    rw [e]
    by_cases c : u * g ∈ K
    · rw [Set.indicator_of_mem (by exact_mod_cast m.2 c), Set.indicator_of_mem (by exact_mod_cast c)]
      rfl
    · rw [Set.indicator_of_notMem (by exact_mod_cast fun d => c (m.1 d)), Set.indicator_of_notMem (by exact_mod_cast c)]
  have hθu' : θ u⁻¹ = u := by rw [← hθu, hθi]
  refine ⟨?_, fun h hh => ?_, fun h hh => ?_⟩
  · calc (Ru * A) * (Ru * A) = Ru * (A * Ru) * A := by simp only [mul_assoc]
      _ = (Ru * Ru') * (A * A) := by rw [hAR]; simp only [mul_assoc]
      _ = 1 := by rw [hRR, hAA, one_mul]
  · have hf : IsHecke K (fun g => h (θ g)) := hecke_comp hθc hθi hθm hθK hh
    have hf' : IsHecke K (fun g => h (u * θ g * u⁻¹)) := by
      refine hecke_comp (φ := fun g => u * θ g * u⁻¹) (by fun_prop) (fun g => ?_) (fun a b => ?_) (fun k hk => ?_) hh
      · show u * θ (u * θ g * u⁻¹) * u⁻¹ = g
        rw [hθm, hθm, hθu, hθu', hθi]
        group
      · show u * θ (a * b) * u⁻¹ = u * θ a * u⁻¹ * (u * θ b * u⁻¹)
        rw [hθm]
        group
      · exact (hu _).1 (hθK k hk)
    have e : Ru * r (fun g => h (θ g)) = r (fun g => h (u * θ g * u⁻¹)) * Ru := by
      refine LinearMap.ext fun y => Subtype.ext ?_
      show (Ru (r (fun g => h (θ g)) y) : V) = (r (fun g => h (u * θ g * u⁻¹)) (Ru y) : V)
      obtain ⟨p1, p2, -⟩ := Sh u hu _ hf
      obtain ⟨q1, q2, -⟩ := Sh u hu _ hf'
      obtain ⟨-, -, e1, -⟩ := (Sh u hu _ hf).2.2.2 y (hY y.2)
      obtain ⟨-, e2, -, -⟩ := (Sh u hu _ hf').2.2.2 y (hY y.2)
      have ef : (fun g => h (θ (u⁻¹ * g))) = fun g => h (u * θ (g * u⁻¹) * u⁻¹) := by
        funext g
        rw [hθm, hθm, hθu']
        congr 1
        group
      rw [b1, hact _ hf, hact _ hf', b1, ← e1, ← e2, ef]
    calc (Ru * A) * r h = Ru * (A * r h) := by rw [mul_assoc]
      _ = (Ru * r (fun g => h (θ g))) * A := by rw [hA h hh, mul_assoc]
      _ = r (fun g => h (u * θ g * u⁻¹)) * (Ru * A) := by rw [e, mul_assoc]
  · obtain ⟨p1, -⟩ := Sh u hu h hh
    refine ⟨p1, LinearMap.ext fun y => Subtype.ext ?_⟩
    show (r (fun g => h (g * u⁻¹)) y : V) = (r h (Ru y) : V)
    obtain ⟨-, e2, -, -⟩ := (Sh u hu h hh).2.2.2 y (hY y.2)
    rw [hact _ p1, hact _ hh, b1, e2]

theorem UpperTheory.V.Z.Mult.Pi.toYdA :
    SlotBasic → LevTop → TranslF → HeckeSum → LvShift → UpperTheory.V.Z.Mult.Pi.ToYdA := by
  intro hSl hLT hTF hHS hLS E _ _ _ n S Z N hS hZ hG π u hu
  obtain ⟨hO, hC, -, hNm⟩ := hLT E n S Z N hS hZ hG
  obtain ⟨t1, t2, κ, hκ, t3⟩ := hTF E n u hu
  have hinv := (hSl E n S hS).1
  have hcont := (hSl E n S hS).2.1
  have hthe : ∀ g, thetaF E n g = (ratF E n u)⁻¹ * thF E n g * ratF E n u := by
    intro g
    rw [t1 g]
    group
  have hnorm : ∀ x, x ∈ Lev S N ↔ ratF E n u * x * (ratF E n u)⁻¹ ∈ Lev S N := by
    intro x
    rw [t3 x]
    refine ⟨hNm κ hκ x, fun hx => ?_⟩
    have := hNm κ⁻¹ ((Kf E n).inv_mem hκ) _ hx
    simpa [mul_assoc] using this
  have hθK : ∀ k ∈ Lev S N, thetaF E n k ∈ Lev S N := by
    intro k hk
    refine (hnorm _).2 ?_
    have e : ratF E n u * thetaF E n k * (ratF E n u)⁻¹ = thF E n k := (t1 k).symm
    rw [e]
    exact (hLT E n S Z N hS hZ hG).2.2.1 k hk
  refine ⟨hθK, ?_⟩
  intro μf hμ Y ρ A hYπ hfd hne hfix hAct hsim hAA hAθ
  have hθm : ∀ a b, thetaF E n (a * b) = thetaF E n a * thetaF E n b := by
    intro a b
    simp only [hthe, map_mul]
    group
  have hθi : ∀ g, thetaF E n (thetaF E n g) = g := by
    intro g
    simp only [hthe, map_mul, map_inv, t2, hinv]
    group
  have hθu : thetaF E n (ratF E n u) = (ratF E n u)⁻¹ := by
    rw [hthe, t2]
    group
  have hθc : Continuous (thetaF E n) := by
    have : thetaF E n = fun g => (ratF E n u)⁻¹ * thF E n g * ratF E n u := funext hthe
    rw [this]
    exact (continuous_const.mul hcont).mul continuous_const
  have hv : (μf (Lev S N : Set (GF E n))).toReal ≠ 0 := by
    haveI := hμ
    exact (ENNReal.toReal_pos (hO.measure_pos μf ⟨1, (Lev S N).one_mem⟩).ne' hC.measure_lt_top.ne).ne'
  obtain ⟨v, hvdef⟩ : ∃ v : ℂ, v = (((μf (Lev S N : Set (GF E n))).toReal : ℝ) : ℂ) := ⟨_, rfl⟩
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    exact_mod_cast hv
  have toF : ∀ {h : GF E n → ℂ}, IsHecke (Lev S N) h → IsHeckeF (Lev S N) h := fun hh =>
    ⟨hh.1, fun k₁ h₁ k₂ h₂ g => by rw [(hh.2 _ h₂ _).2, (hh.2 _ h₁ _).1]⟩
  have toH : ∀ {h : GF E n → ℂ}, IsHeckeF (Lev S N) h → IsHecke (Lev S N) h := fun hh =>
    ⟨hh.1, fun k hk x => ⟨by simpa using hh.2 k hk 1 (Lev S N).one_mem x,
      by simpa using hh.2 1 (Lev S N).one_mem k hk x⟩⟩
  have hY : Y ≤ fixed (finRep E n) (Lev S N) := fun y hy k => by
    simpa using hfix y hy k k.2
  have hact : ∀ h, IsHecke (Lev S N) h → ∀ y : Y,
      (((v⁻¹ • ρ h : Module.End ℂ Y) y : Y) : Sm E n) = Lv (finRep E n) (Lev S N) h y := by
    intro h hh y
    have e : ((ρ h y : Y) : Sm E n) = v • Lv (finRep E n) (Lev S N) h y := by
      refine Subtype.ext ?_
      have e1 := hAct h (toF hh) y
      have e2 := hHS E n (Lev S N) hO hC μf hμ h hh y (hY y.2)
      rw [e1, e2, hvdef]
      rfl
    show ((v⁻¹ • (ρ h y) : Y) : Sm E n) = _
    rw [Submodule.coe_smul, e, inv_smul_smul₀ hv0]
  obtain ⟨c1, c2, c3⟩ := core hLS (finRep E n) (Lev S N) hO hC (ratF E n u) hnorm (thetaF E n) hθc hθi hθm hθK hθu
    Y hY (fun h => v⁻¹ • ρ h) hact A hAA (fun h hh => by
      rw [mul_smul_comm, smul_mul_assoc, hAθ h (toF hh)])
  refine ⟨⟨Y, fun h => v⁻¹ • ρ h, _, hYπ, hfd, hne, hY, hact, ?_, c1, ?_⟩, v, hvdef, fun h hh =>
    ⟨toF (c3 h hh).1, ?_⟩⟩
  · intro W hW
    refine hsim W fun h hh y hy => ?_
    exact (W.smul_mem_iff (inv_ne_zero hv0)).1 (hW h (toH hh) y hy)
  · intro h hh
    have e : (fun g => h (thF E n g)) = fun g => h (ratF E n u * thetaF E n g * (ratF E n u)⁻¹) :=
      funext fun g => by rw [t1 g]
    show _ * _ = (v⁻¹ • ρ (fun g => h (thF E n g))) * _
    rw [e]
    exact c2 h hh
  · have e2 : v⁻¹ • ρ (fun g => h (g * (ratF E n u)⁻¹)) = (v⁻¹ • ρ h) *
        (v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) := (c3 h hh).2
    have key : ρ (fun g => h (g * (ratF E n u)⁻¹)) * A = v • ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [← mul_assoc, ← e2, smul_mul_assoc, smul_inv_smul₀ hv0]
    have tr : LinearMap.trace ℂ Y (ρ (fun g => h (g * (ratF E n u)⁻¹)) * A) = v * LinearMap.trace ℂ Y ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [key, LinearMap.map_smul, smul_eq_mul]
    exact tr
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi

private theorem relIndex_positions {G ι : Type} [Group G] {A : ι → Type} [∀ i, Group (A i)] (K : Subgroup G)
    (q : ∀ i, G →* A i) (j : ∀ i, A i →* G) (B N : ∀ i, Subgroup (A i)) (T : Finset ι)
    (hqj : ∀ i ∈ T, ∀ a, q i (j i a) = a)
    (hqk : ∀ i ∈ T, ∀ k ∈ T, i ≠ k → ∀ a, q k (j i a) = 1)
    (hj : ∀ i ∈ T, ∀ a ∈ B i, j i a ∈ K)
    (hq : ∀ i ∈ T, ∀ k ∈ K, q i k ∈ B i) :
    (K ⊓ ⨅ i ∈ T, (N i).comap (q i)).relIndex K = ∏ i ∈ T, (N i).relIndex (B i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    have ih' := ih (fun k hk => hqj k (Finset.mem_insert_of_mem hk))
      (fun k hk l hl => hqk k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl))
      (fun k hk => hj k (Finset.mem_insert_of_mem hk))
      (fun k hk => hq k (Finset.mem_insert_of_mem hk))
    have hiT : i ∈ insert i T := Finset.mem_insert_self i T
    set L : Subgroup G := K ⊓ ⨅ k ∈ T, (N k).comap (q k) with hL
    have hins : (K ⊓ ⨅ k ∈ insert i T, (N k).comap (q k)) = L ⊓ (N i).comap (q i) := by
      rw [Finset.iInf_insert, inf_left_comm, inf_comm]
    have hmap : L.map (q i) = B i := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hq i hiT x (Subgroup.mem_inf.1 hx).1
      · intro a ha
        refine ⟨j i a, ?_, hqj i hiT a⟩
        refine Subgroup.mem_inf.2 ⟨hj i hiT a ha, ?_⟩
        simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
        intro k hk
        have hne : i ≠ k := fun h => hi (h ▸ hk)
        rw [hqk i hiT k (Finset.mem_insert_of_mem hk) hne a]
        exact (N k).one_mem
    rw [hins, Finset.prod_insert hi, ← ih',
      ← Subgroup.relIndex_mul_relIndex (L ⊓ (N i).comap (q i)) L K inf_le_left inf_le_left,
      Subgroup.inf_relIndex_left, Subgroup.relIndex_comap, hmap]

private theorem mem_Lev {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ}
    (S : Set (GlobalTheory.BCT.Pl E)) (N : ∀ w : GlobalTheory.BCT.Pl E, Subgroup (GlobalTheory.BCT.GLw n w)) (g : GF E n) :
    g ∈ Lev S N ↔ ∀ i, Sl S i → qw n i.1 i.2 g ∈ N i.1 := by
  unfold Lev
  rw [Subgroup.mem_iInf]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.1 i.2⟩

theorem levIdx_pf :
    SlotBasic → LevTop → LevIdx := by
  intro hF _ E _ _ _ n S Z N hS hZ hG
  obtain ⟨-, -, h3, h4, -, -, h7⟩ := hF E n S hS
  have hK : ∀ g, g ∈ PositivityTheory.Rg.BcB.G8.Kf E n ↔ ∀ i, Sl S i → qw n i.1 i.2 g ∈ GlobalTheory.LFun.KGL i.1 (n := n) := fun g => by
    rw [← h7, mem_Lev]
  have hLe : Lev S N ≤ PositivityTheory.Rg.BcB.G8.Kf E n := fun g hg =>
    (hK g).2 fun i hi => (hG i.1).2.1 ((mem_Lev S N g).1 hg i hi)
  refine ⟨hLe, ?_⟩
  have hposition : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), Sl S i := fun i hi => by
    have hw := hZ i.1 (Finset.mem_product.1 hi).1
    exact ⟨hw.1, fun _ => hw.2⟩
  have hEq : Lev S N = PositivityTheory.Rg.BcB.G8.Kf E n ⊓ ⨅ i ∈ Z ×ˢ (Finset.univ : Finset Bool),
      (N i.1).comap (qw n i.1 i.2) := by
    apply le_antisymm
    · intro g hg
      refine Subgroup.mem_inf.2 ⟨hLe hg, ?_⟩
      simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
      exact fun i hi => (mem_Lev S N g).1 hg i (hposition i hi)
    · intro g hgg
      obtain ⟨hg, hg'⟩ := Subgroup.mem_inf.1 hgg
      simp only [Subgroup.mem_iInf, Subgroup.mem_comap] at hg'
      refine (mem_Lev S N g).2 fun i hi => ?_
      by_cases hw : i.1 ∈ Z
      · exact hg' i (Finset.mem_product.2 ⟨hw, Finset.mem_univ _⟩)
      · rw [(hG i.1).2.2.2 hw]
        exact (hK g).1 hg i hi
  have key := relIndex_positions (A := fun i : GlobalTheory.BCT.Pl E × Bool => GlobalTheory.BCT.GLw n i.1) (PositivityTheory.Rg.BcB.G8.Kf E n)
    (fun i => qw n i.1 i.2) (fun i => jw n i.1 i.2) (fun i => GlobalTheory.LFun.KGL i.1 (n := n)) (fun i => N i.1)
    (Z ×ˢ (Finset.univ : Finset Bool))
    (fun i _ a => (h3 i.1 i.2).2.2.1 a)
    (fun i hi k hk hne a => h4 i k (hposition i hi) (hposition k hk) hne a)
    (fun i hi a ha => (hK _).2 fun k hk => by
      by_cases hik : i = k
      · subst hik
        rw [(h3 i.1 i.2).2.2.1 a]
        exact ha
      · rw [h4 i k (hposition i hi) hk hik a]
        exact (GlobalTheory.LFun.KGL k.1 (n := n)).one_mem)
    (fun i hi k hk => (hK k).1 hk i (hposition i hi))
  rw [hEq, key, Finset.prod_product]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp [Fintype.prod_bool, sq]

end UpperTheory.V.Z.Mult.Pi
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

private theorem haar_measure_rel_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (μ : MeasureTheory.Measure Γ) [μ.IsHaarMeasure]
    (K K' : Subgroup Γ) (hK' : IsOpen (K' : Set Γ)) (hK : IsCompact (K : Set Γ)) (hle : K' ≤ K) :
    (μ K').toReal * (K'.relIndex K : ℕ) = (μ K).toReal := by
  classical
  have hopen : ∀ g : Γ, IsOpen ((fun x => g⁻¹ * x) ⁻¹' (K' : Set Γ)) := fun g =>
    hK'.preimage (continuous_const.mul continuous_id)
  have hcov : (K : Set Γ) ⊆ ⋃ k : K, (fun x => (k : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    simp [K'.one_mem]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (fun k : K => hopen (k : Γ)) hcov
  have hmem : ∀ a b : K, ((a : Γ)⁻¹ * (b : Γ) ∈ K') ↔
      (QuotientGroup.mk a : K ⧸ K'.subgroupOf K) = QuotientGroup.mk b := by
    intro a b
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hfin : Finite (K ⧸ K'.subgroupOf K) := by
    refine Finite.of_surjective
      (fun k : t => (QuotientGroup.mk (k : K) : K ⧸ K'.subgroupOf K)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.1 (ht x.2)
      exact ⟨⟨k, hk⟩, (hmem k x).1 hx⟩
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let s : K ⧸ K'.subgroupOf K → K := Quotient.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ K'.subgroupOf K) = q := fun q =>
    QuotientGroup.out_eq' q
  let f : K ⧸ K'.subgroupOf K → Set Γ := fun q =>
    (fun x => ((s q : K) : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ)
  have hU : (K : Set Γ) = ⋃ q, f q := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.2 ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      exact (hmem _ ⟨x, hx⟩).2 (hs _)
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
      have h1 : ((s q : K) : Γ)⁻¹ * x ∈ K := hle hq
      have h2 := K.mul_mem (s q).2 h1
      simpa using h2
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro p q hpq
    refine Set.disjoint_left.2 ?_
    intro x hp hq
    apply hpq
    have hp' : ((s p : K) : Γ)⁻¹ * x ∈ K' := hp
    have hq' : ((s q : K) : Γ)⁻¹ * x ∈ K' := hq
    have h3 : ((s p : K) : Γ)⁻¹ * (s q : K) ∈ K' := by
      have := K'.mul_mem hp' (K'.inv_mem hq')
      simpa [mul_assoc] using this
    rw [← hs p, ← hs q]
    exact (hmem _ _).1 h3
  have hμ : ∀ q, μ (f q) = μ K' := fun q =>
    MeasureTheory.measure_preimage_mul μ _ _
  have hsum := MeasureTheory.measure_iUnion (μ := μ) hdisj (fun q => (hopen _).measurableSet)
  rw [← hU, tsum_fintype] at hsum
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hsum, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm]
  simp only [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

theorem UpperTheory.V.Z.Mult.Pi.volIdx_pf :
    VolIdx := by
  intro Γ _ _ _ _ _ μ _ K K' hK' hK hle
  exact haar_measure_rel_index μ K K' hK' hK hle
end
