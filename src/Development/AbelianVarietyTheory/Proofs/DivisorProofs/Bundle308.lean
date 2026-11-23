module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle204
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle181
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle207
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle210
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle209
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Support
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Fourier.Notation
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Complex.Basic
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

section

open Matrix

namespace GlobalTheory.CharDotKill

theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.KeyLemmaTwo.main
  | exact _root_.GlobalTheory.KeyLemmaTwo.main
  | (apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KeyLemmaTwo.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KeyLemmaTwo.main ..)

theorem exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : ∃ U : OpenAddSubgroup K, ∀ t ∈ U, ψ t = 1 := by
  have hV : {t : K | ‖ψ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

theorem nonarchimedean_pi {κ K : Type} [Finite κ] [AddCommGroup K] [TopologicalSpace K]
    [NonarchimedeanAddGroup K] : NonarchimedeanAddGroup (κ → K) where
  is_nonarchimedean S hS := by
    rw [nhds_pi, Filter.mem_pi] at hS
    obtain ⟨I, -, t, ht, hsub⟩ := hS
    choose M hM using fun i => NonarchimedeanAddGroup.is_nonarchimedean _ (ht i)
    refine ⟨⟨AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup, ?_⟩, ?_⟩
    · change IsOpen ((AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup : AddSubgroup (κ → K)) : Set (κ → K))
      rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (M i).isOpen
    · intro x hx
      apply hsub
      intro i _
      exact hM i (hx i (Set.mem_univ i))

theorem charDot_kill : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ]
    (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K),
      ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  intro K _ _ _ _ χ hχ κ _ C hC
  obtain ⟨K₀, hK₀⟩ := exists_open_ker χ hχ
  have hdot : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hO : IsOpen {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} :=
    K₀.isOpen.preimage hdot

  have hW : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ (K₀ : Set K) := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    have hO' : IsOpen {p : (κ → K) × (κ → K) | p.2 ⬝ᵥ p.1 ∈ (K₀ : Set K)} :=
      K₀.isOpen.preimage (continuous_snd.dotProduct continuous_fst)
    filter_upwards [hO'.mem_nhds (x := ((0 : κ → K), z)) (by simp [K₀.zero_mem])] with p hp
    exact hp

  have hP : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} ∈ nhds ((0 : κ → K), (0 : κ → K)) :=
    hO.mem_nhds (by simp [K₀.zero_mem])
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hP
  obtain ⟨U, hU, V, hV, hUV⟩ := hP
  haveI : NonarchimedeanAddGroup (κ → K) := nonarchimedean_pi
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (Filter.inter_mem (Filter.inter_mem hU hV) hW)
  refine ⟨H, fun z hz a ha b hb => hK₀ _ (K₀.add_mem ?_ ?_)⟩
  · exact (hH hb).2 z hz
  · exact hUV (Set.mk_mem_prod (hH ha).1.1 (hH hb).1.2)

end GlobalTheory.CharDotKill
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem norm_le_lintegral_ray_iteratedFDeriv
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hdec : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) :
    ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
      (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hL
  have hLt : ∀ t : ℝ, L t = t • v := fun t => by simp [hL]
  set Gx : E → F := fun z => G (x + z) with hGx
  have hGx' : ContDiff ℝ (⊤ : ℕ∞) Gx := hG.comp (contDiff_const.add contDiff_id)
  set h : ℝ → F := Gx ∘ L with hh
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h := hGx'.comp L.contDiff
  have key : ∀ (j : ℕ) (t : ℝ),
      iteratedDeriv j h t = iteratedFDeriv ℝ j G (x + t • v) (fun _ => v) := by
    intro j t
    rw [iteratedDeriv_eq_iteratedFDeriv, hh,
      L.iteratedFDeriv_comp_right hGx' t (by exact_mod_cast le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, hGx,
      iteratedFDeriv_comp_add_left, hLt]
    simp [hLt]
  have bound : ∀ (j : ℕ) (t : ℝ),
      ‖iteratedDeriv j h t‖ ≤ ‖iteratedFDeriv ℝ j G (x + t • v)‖ * ‖v‖ ^ j := by
    intro j t
    rw [key]
    refine ((iteratedFDeriv ℝ j G (x + t • v)).le_opNorm _).trans (le_of_eq ?_)
    simp [Finset.prod_const]
  have hdec' : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0) := by
    intro j hj
    refine squeeze_zero_norm (fun t => bound j t) ?_
    have := ((hdec j hj).norm).mul_const (‖v‖ ^ j)
    simpa using this
  have h0 : h 0 = G x := by simp [hh, hGx, hLt]
  have main := GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv h m hhs hdec'
  rw [h0] at main
  refine main.trans (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ha : 0 ≤ t ^ m / (m.factorial : ℝ) := by
    have : (0:ℝ) < t := ht
    positivity
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul ha]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ha)
  rw [mul_comm]
  exact bound (m + 1) t

end GlobalTheory
end

section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : SchwartzMap E ℂ),
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  first | exact @GlobalTheory.GaussCutoff.mem_closure_gauss_mul | exact GlobalTheory.GaussCutoff.mem_closure_gauss_mul | (intros; apply GlobalTheory.GaussCutoff.mem_closure_gauss_mul <;> assumption)
end

section


theorem _root_.GlobalTheory.T.sum_primes_inv_pred_le_loglog : ∀ y : ℕ, 3 ≤ y → ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ 7 * Real.log (Real.log y) + 6 := by
  first | exact @GlobalTheory.PrimeRecipSum.sum_inv_pred_le | exact GlobalTheory.PrimeRecipSum.sum_inv_pred_le | (intros; apply GlobalTheory.PrimeRecipSum.sum_inv_pred_le <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isRoot_map_minpoly_iff_exists_ringHom_extension : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by
  first | exact @GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom | exact GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom | (intros; apply GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetFourier

theorem star_eq_inv_of_pow_eq_one {w : ℂ} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n = 1) :
    star w = w⁻¹ := by
  have h1 : ‖w‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw hn
  have h2 : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [Complex.inv_def, h2]; simp [Complex.star_def]

theorem geom_sum_root_of_unity {w : ℂ} {n : ℕ} (hw : w ^ n = 1) :
    ∑ a ∈ Finset.range n, w ^ a = if w = 1 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · rw [geom_sum_eq h, hw]; simp

theorem fourier_coset_sums : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  intro G Γ _ _ _ _ φ s hs ζ hζ
  have hn0 : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hs
  let u : ℂˣ := Units.mk0 ζ (hζ.ne_zero hn0)
  have hu : orderOf u ∣ orderOf s := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hord]; ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Units.val_mk0]
    exact hζ.pow_eq_one
  let η₀ : Γ →* ℂˣ := monoidHomOfForallMemZpowers hs hu
  have hη₀s : η₀ s = u := monoidHomOfForallMemZpowers_apply_gen hs hu
  have hinj : Function.Injective η₀ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs t)
    rw [map_zpow, hη₀s] at ht
    have hk : ζ ^ k = 1 := by
      have := congrArg Units.val ht
      simpa [u, Units.val_zpow_eq_zpow_val] using this
    rw [hζ.zpow_eq_one_iff_dvd] at hk
    rw [← orderOf_dvd_iff_zpow_eq_one, hord]; exact hk
  let η : G ⋊[φ] Γ →* ℂˣ := η₀.comp rightHom
  have hηx : ∀ x, η x = η₀ x.right := fun x => rfl
  have hpow : ∀ x, (η x : ℂ) ^ Nat.card Γ = 1 := by
    intro x
    rw [hηx, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one']; simp
  have hstar : ∀ x, star (η x : ℂ) = (η x : ℂ)⁻¹ := fun x => star_eq_inv_of_pow_eq_one hn0 (hpow x)
  have hone : ∀ x : G ⋊[φ] Γ, (η x : ℂ)⁻¹ = 1 ↔ x.right = 1 := by
    intro x
    rw [inv_eq_one, Units.val_eq_one, hηx, ← map_one η₀, hinj.eq_iff]
  have hzeta : ∀ x : G ⋊[φ] Γ, ζ * (η x : ℂ)⁻¹ = 1 ↔ x.right = s := by
    intro x
    have hne : (η x : ℂ) ≠ 0 := (η x).ne_zero
    rw [mul_inv_eq_one₀ hne, eq_comm, hηx]
    have : ζ = ((η₀ s : ℂˣ) : ℂ) := by rw [hη₀s]; rfl
    rw [this, Units.val_inj, hinj.eq_iff]
  refine ⟨η, fun g => by simp [η], by rw [show η (inr s) = η₀ s from by simp [η], hη₀s]; rfl, ?_⟩
  intro X Y
  haveI : Fintype G := Fintype.ofFinite G
  let e : G ⋊[φ] Γ ≃ G × Γ :=
    ⟨fun x => (x.left, x.right), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
  haveI : Fintype (G ⋊[φ] Γ) := Fintype.ofEquiv (G × Γ) e.symm

  have key : ∀ (c : ℂ) (t : Γ), (∀ x : G ⋊[φ] Γ, c * (η x : ℂ)⁻¹ = 1 ↔ x.right = t) →
      c ^ Nat.card Γ = 1 →
      ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) =
        (Nat.card Γ : ℂ) * ∑ g : G, X ⟨g, t⟩ * star (Y ⟨g, t⟩) := by
    intro c t hct hc
    simp_rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ x : G ⋊[φ] Γ, ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * (X x * star (Y x * (η x : ℂ) ^ a))
        = X x * star (Y x) * (if x.right = t then (Nat.card Γ : ℂ) else 0) := by
      intro x
      have : ∀ a, c ^ a * (X x * star (Y x * (η x : ℂ) ^ a)) = X x * star (Y x) * (c * (η x : ℂ)⁻¹) ^ a := by
        intro a
        rw [star_mul', star_pow, hstar, mul_pow]; ring
      simp_rw [this]
      rw [← Finset.mul_sum, geom_sum_root_of_unity (by rw [mul_pow, inv_pow, hc, hpow, inv_one, one_mul])]
      simp only [hct]
    simp_rw [hterm]
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [e, mul_comm]
  refine ⟨?_, ?_⟩
  · have := key 1 1 (fun x => by rw [one_mul]; exact hone x) (one_pow _)
    simp only [one_pow, one_mul] at this
    rw [this, finsum_eq_sum_of_fintype]
    rfl
  · rw [key ζ s hzeta hζ.pow_eq_one, finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    have : (inl g * inr s : G ⋊[φ] Γ) = ⟨g, s⟩ := by ext <;> simp
    rw [this]

end GlobalTheory.Shin.CosetFourier
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory

theorem finiteDim_functions_detected_by_finset (K : Type) (W : Submodule ℂ (K → ℂ))
    (hW : FiniteDimensional ℂ W) :
    ∃ s : Finset K, ∀ w ∈ W, (∀ k ∈ s, w k = 0) → w = 0 := by
  classical
  haveI := hW
  let N : Finset K → Submodule ℂ (K → ℂ) := fun s =>
    W ⊓ ⨅ k ∈ s, LinearMap.ker (LinearMap.proj k : (K → ℂ) →ₗ[ℂ] ℂ)
  have memN : ∀ s w, w ∈ N s ↔ w ∈ W ∧ ∀ k ∈ s, w k = 0 := by
    intro s w
    simp [N, Submodule.mem_iInf]
  have hex : ∃ n, ∃ s : Finset K, Module.finrank ℂ (N s) = n := ⟨_, ∅, rfl⟩
  obtain ⟨s0, hs0⟩ := Nat.find_spec hex
  have hmin : ∀ s : Finset K, Nat.find hex ≤ Module.finrank ℂ (N s) :=
    fun s => Nat.find_min' hex ⟨s, rfl⟩
  have hfin : ∀ s, FiniteDimensional ℂ (N s) := fun s =>
    Submodule.finiteDimensional_of_le (inf_le_left)
  refine ⟨s0, fun w hw hvan => ?_⟩
  have hwN : w ∈ N s0 := (memN s0 w).2 ⟨hw, hvan⟩
  funext k
  have hle : N (insert k s0) ≤ N s0 := by
    intro v hv
    rw [memN] at hv ⊢
    exact ⟨hv.1, fun j hj => hv.2 j (Finset.mem_insert_of_mem hj)⟩
  have heq : N (insert k s0) = N s0 :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hs0]; exact hmin _)
  rw [← heq, memN] at hwN
  exact hwN.2 k (Finset.mem_insert_self k s0)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.representations_equal_traces_conjugate : ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m → ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ), (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  first | exact @GlobalTheory.conj_of_trace_central_idem_eq | exact GlobalTheory.conj_of_trace_central_idem_eq | (intros; apply GlobalTheory.conj_of_trace_central_idem_eq <;> assumption)
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  first | exact @GlobalTheory.SympBlocks.det_ne_zero_and_isSymm | exact GlobalTheory.SympBlocks.det_ne_zero_and_isSymm | (intros; apply GlobalTheory.SympBlocks.det_ne_zero_and_isSymm <;> assumption)
end

section

namespace GlobalTheory

theorem exists_ne_zero_forall_complexPoint_separate
    (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
    [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F)
    (h : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A))
    (hinj : Function.Injective (j₁.comp (algebraMap B A))) (a : A) (ha : j₁ a ≠ j₂ a) :
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ,
      y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  classical
  letI : Algebra B F := (j₁.comp (algebraMap B A)).toAlgebra
  let J₁ : A →ₐ[B] F := { j₁ with commutes' := fun _ => rfl }
  let J₂ : A →ₐ[B] F := { j₂ with commutes' := fun b => (RingHom.congr_fun h b).symm }
  let u : F := (j₁ a - j₂ a)⁻¹
  let D : Subalgebra B F := (Subalgebra.map J₁ ⊤ ⊔ Subalgebra.map J₂ ⊤) ⊔
    Algebra.adjoin B (({u} : Finset F) : Set F)
  have hA : (⊤ : Subalgebra B A).FG := Algebra.FiniteType.out
  have hD : D.FG := ((hA.map J₁).sup (hA.map J₂)).sup (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FiniteType B D := (Subalgebra.fg_iff_finiteType D).1 hD
  have h1 : ∀ x, J₁ x ∈ D := fun x =>
    (le_sup_left.trans le_sup_left : Subalgebra.map J₁ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have h2 : ∀ x, J₂ x ∈ D := fun x =>
    (le_sup_right.trans le_sup_left : Subalgebra.map J₂ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have hu : u ∈ D := (le_sup_right : _ ≤ D) (Algebra.subset_adjoin (by simp))
  have hBD : Function.Injective (algebraMap B D) := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  obtain ⟨q, hq, H⟩ := GlobalTheory.exists_ne_zero_forall_complexPoint_extend B D hBD
  refine ⟨q, hq, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := H φ hφ
  let K₁ : A →ₐ[B] D := J₁.codRestrict D h1
  let K₂ : A →ₐ[B] D := J₂.codRestrict D h2
  refine ⟨ψ.comp (K₁ : A →+* D), ψ.comp (K₂ : A →+* D), ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · intro heq
    have hone : (⟨u, hu⟩ : D) * (K₁ a - K₂ a) = 1 :=
      Subtype.ext (inv_mul_cancel₀ (sub_ne_zero.2 ha))
    have h3 := congrArg ψ hone
    have heq' : ψ (K₁ a) = ψ (K₂ a) := heq
    rw [map_mul, map_sub, heq', sub_self, mul_zero, map_one] at h3
    exact zero_ne_one h3

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_ne_zero_forall_complexPoint_extend' : ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by
  first | exact @GlobalTheory.exists_ne_zero_forall_complexPoint_extend | exact GlobalTheory.exists_ne_zero_forall_complexPoint_extend | (intros; apply GlobalTheory.exists_ne_zero_forall_complexPoint_extend <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.mem_support_quotient_span_iff_of_isPushout' : ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'), IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'), ((letI := qa'.hom.toAlgebra; p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔ (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first | (exact @GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (exact GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (intros; apply GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout  <;> assumption)
end
