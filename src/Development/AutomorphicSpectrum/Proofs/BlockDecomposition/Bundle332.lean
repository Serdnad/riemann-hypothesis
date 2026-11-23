module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle150
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.AvgBox

theorem setIntegral_eq_sum_reps {E : Type} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    (μ : Measure E) [μ.IsAddLeftInvariant] (D M : AddSubgroup E) (hD : MeasurableSet (D : Set E))
    (hfin : μ (D : Set E) ≠ ⊤) (hDM : D ≤ M) (S : Finset E) (hSM : ∀ s ∈ S, s ∈ M)
    (hS : ∀ x ∈ M, ∃! s, s ∈ S ∧ x - s ∈ D) (f : E → ℂ) (hf : ∀ x, ∀ d ∈ D, f (x + d) = f x) :
    ∫ x in (M : Set E), f x ∂μ = ((μ.real (D : Set E) : ℝ) : ℂ) * ∑ s ∈ S, f s := by
  classical
  set A : E → Set E := fun s => (fun x => -s + x) ⁻¹' (D : Set E) with hA
  have hAm : ∀ s, MeasurableSet (A s) := fun s => (measurable_const_add (-s)) hD
  have hmem : ∀ s x, x ∈ A s ↔ x - s ∈ D := by
    intro s x
    simp only [hA, Set.mem_preimage, SetLike.mem_coe, neg_add_eq_sub]
  have hAM : ∀ s ∈ S, ∀ x ∈ A s, x ∈ M := by
    intro s hs x hx
    have := M.add_mem (hDM ((hmem s x).1 hx)) (hSM s hs)
    simpa using this
  have hU : (M : Set E) = ⋃ s ∈ S, A s := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    constructor
    · intro hx
      obtain ⟨s, ⟨hs, hxs⟩, -⟩ := hS x hx
      exact ⟨s, hs, (hmem s x).2 hxs⟩
    · rintro ⟨s, hs, hx⟩
      exact hAM s hs x hx
  have hdisj : Set.Pairwise (S : Set E) (Function.onFun Disjoint A) := by
    intro s hs s' hs' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    exact (hS x (hAM s hs x hx)).unique ⟨hs, (hmem s x).1 hx⟩ ⟨hs', (hmem s' x).1 hx'⟩
  have hconst : ∀ s, Set.EqOn (fun _ => f s) f (A s) := by
    intro s x hx
    have := hf s (x - s) ((hmem s x).1 hx)
    simpa using this.symm
  have hvol : ∀ s, μ (A s) = μ (D : Set E) := fun s => measure_preimage_add μ (-s) _
  rw [hU, integral_biUnion_finset S (fun s _ => hAm s) hdisj ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← setIntegral_congr_fun (hAm s) (hconst s), setIntegral_const]
    simp [Measure.real, hvol]
  · intro s _
    refine IntegrableOn.congr_fun ?_ (hconst s) (hAm s)
    exact integrableOn_const (by rw [hvol]; exact hfin)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem sub_smul_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (y : Fin (n + 1) → k) (v : V) :
    T (uM (n + 1) y) v - ((ψ (y (Fin.last n)) : Circle) : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  let x : MirUin k (n + 1) := ⟨uM (n + 1) y, Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd y, rfl⟩⟩
  have hx := mirChar_eq k ψ n x (Multiplicative.ofAdd y) rfl
  refine Submodule.subset_span ⟨x, v, ?_⟩
  rw [hx]
  rfl

theorem wt_mul_psi (ψ : AddChar k Circle) (y : Fin (n + 1) → k) :
    wt ψ n y * ((ψ (y (Fin.last n)) : Circle) : ℂ) = 1 := by
  rw [wt, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  simp

theorem avg_sub_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (S : Finset (Fin (n + 1) → k)) (v : V) :
    (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  have h : (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v =
      ∑ s ∈ S, wt ψ n s • (T (uM (n + 1) s) v - ((ψ (s (Fin.last n)) : Circle) : ℂ) • v) := by
    simp only [smul_sub, smul_smul, wt_mul_psi, one_smul, Finset.sum_sub_distrib, Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (sub_smul_mem_twKer ψ T s v)

theorem integrand_add (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (v : V) (v' : V') (x d : Fin (n + 1) → k) (hd : T (uM (n + 1) d) v = v)
    (hψ : ψ (d (Fin.last n)) = 1) :
    wt ψ n (x + d) * coef T B v v' (x + d) = wt ψ n x * coef T B v v' x := by
  have h1 : wt ψ n (x + d) = wt ψ n x := by
    simp only [wt, Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, hψ, inv_one, mul_one]
  have h2 : coef T B v v' (x + d) = coef T B v v' x := by
    simp only [coef, uM_add, map_mul, Module.End.mul_apply, hd]
  rw [h1, h2]

end Rep

theorem exists_JJ_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → ∃ v', JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT hB v hv
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : (piHaar ν (n + 1)).IsAddHaarMeasure := by
    unfold piHaar
    infer_instance
  obtain ⟨r, hr⟩ := exists_cball_addChar_eq_one ψ hψ
  have hΩ₁ : {y : Fin (n + 1) → k | T (uM (n + 1) y) v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    refine ((hT v).preimage (continuous_uM (n + 1))).mem_nhds ?_
    simp [uM]
  have hΩ₂ : {y : Fin (n + 1) → k | y (Fin.last n) ∈ cball r} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    have h0 : cball r ∈ 𝓝 ((0 : Fin (n + 1) → k) (Fin.last n)) := by simpa using cball_mem_nhds r
    exact (continuous_apply (Fin.last n)).continuousAt h0
  obtain ⟨t₀, ht₀⟩ := exists_box_subset (Filter.inter_mem hΩ₁ hΩ₂)
  refine ⟨t₀, fun t ht => ?_⟩
  have hDM : box (n + 1) t₀ ≤ box (n + 1) t := fun x hx j =>
    show valuation k (x j) ≤ valuation k (t : k) from
      le_trans (show valuation k (x j) ≤ valuation k (t₀ : k) from hx j) ht
  have hDo : IsOpen (box (n + 1) t₀ : Set (Fin (n + 1) → k)) :=
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (box_mem_nhds (n + 1) t₀)
  obtain ⟨S, hSM, hS⟩ := GlobalTheory.CompanionTheory.OpenSubgroupCosets.exists_finset_unique_coset_reps
    (box (n + 1) t₀) hDo (box (n + 1) t : Set (Fin (n + 1) → k)) (isCompact_box (n + 1) t)
  have hfin : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ ⊤ :=
    (isCompact_box (n + 1) t₀).measure_lt_top.ne
  have hpos : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ 0 :=
    hDo.measure_ne_zero _ ⟨0, (box (n + 1) t₀).zero_mem⟩
  have hvol : ((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) ≠ 0 :=
    (ENNReal.toReal_pos hpos hfin).ne'
  have hcard : (S.card : ℂ) ≠ 0 := by
    obtain ⟨s, ⟨hs, -⟩, -⟩ := hS 0 (box (n + 1) t).zero_mem
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs)
  set v₁ : V := ∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v with hv₁
  have hv₁0 : v₁ ≠ 0 := by
    intro h0
    have h := avg_sub_mem_twKer ψ T S v
    rw [← hv₁, h0, zero_sub, neg_mem_iff] at h
    exact hv ((Submodule.smul_mem_iff _ hcard).1 h)
  obtain ⟨v', hv'⟩ := hB v₁ hv₁0
  refine ⟨v', ?_⟩
  have hJ : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' =
      (((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) : ℂ) * B v₁ v' := by
    rw [JJ, setIntegral_eq_sum_reps (piHaar ν (n + 1)) (box (n + 1) t₀) (box (n + 1) t) hDo.measurableSet hfin hDM S
      hSM hS _ fun x d hd => integrand_add ψ T B v v' x d (ht₀ hd).1 (hr _ (ht₀ hd).2)]

    simp only [hv₁, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, coef]
  rw [hJ]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 hvol) hv'

end GlobalTheory.CompanionTheory.MirPair.AvgBox

end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearLat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dotProduct_eLast {n : ℕ} (b : Fin (n + 1) → k) : b ⬝ᵥ eLast k n = b (Fin.last n) := by
  simp [eLast, dotProduct_single]

theorem isUnit_one_add {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0) :
    IsUnit (1 + vecMulVec (eLast k n) b) := by
  rw [Matrix.isUnit_iff_isUnit_det, vecMulVec_eq (ι := Unit),
    det_one_add_replicateCol_mul_replicateRow, dotProduct_eLast]
  exact h.isUnit

theorem shearGL_mulVec {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0)
    (x : Fin (n + 1) → k) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x =
      x + (b ⬝ᵥ x) • eLast k n := by
  have e : ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
    unfold shearGL
    rw [dite_eq_left (isUnit_one_add b h)]
    rfl
  rw [e, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem dotProduct_shear {n : ℕ} (b x : Fin (n + 1) → k) :
    b ⬝ᵥ (x + (b ⬝ᵥ x) • eLast k n) = (1 + b (Fin.last n)) * (b ⬝ᵥ x) := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_eLast, smul_eq_mul]
  ring

theorem exists_bound {n : ℕ} (g : GL (Fin (n + 1)) k) :
    ∃ C : kˣ, 1 ≤ valuation k (C : k) ∧
      (∀ i, valuation k (((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) ≤ valuation k (C : k)) ∧
      ∀ i j, valuation k (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j) ≤
        valuation k (C : k) := by
  let f : Option (Fin (n + 1) ⊕ Fin (n + 1) × Fin (n + 1)) → k := fun o =>
    match o with
    | none => 1
    | some (.inl i) => ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i
    | some (.inr p) => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p.1 p.2
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun o => valuation k (f o)
  have h1 : 1 ≤ valuation k (f i₀) := by simpa [f] using hi₀ none
  have hne : f i₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact absurd h1 (by simp)
  exact ⟨Units.mk0 _ hne, h1, fun i => hi₀ (some (.inl i)), fun i j => hi₀ (some (.inr (i, j)))⟩

theorem mul_mem_cball {a u : k} {p C t : kˣ} (hp : valuation k (p : k) ≤ 1)
    (ha : a ∈ cball (p * C⁻¹ * t)) (hu : valuation k u ≤ valuation k (C : k)) : a * u ∈ cball t := by
  have ha' : valuation k a ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := ha
  show valuation k (a * u) ≤ valuation k (t : k)
  calc valuation k (a * u) = valuation k a * valuation k u := map_mul _ _ _
    _ ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) * valuation k (C : k) := mul_le_mul' ha' hu
    _ = valuation k (p : k) * valuation k (t : k) := by
        rw [← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
    _ ≤ valuation k (t : k) := mul_le_of_le_one_left' hp

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin (n + 1)) k), ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, ∀ (t : kˣ) (x : Fin (n + 1) → k), ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) ∈ box (n + 1) t ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t) := by
  intro k _ _ _ _ n g
  obtain ⟨C, hC1, hu, hH⟩ := exists_bound g
  obtain ⟨p₀, hp0, hp1⟩ : ∃ p : k, p ≠ 0 ∧ valuation k p < 1 := Valuation.IsNontrivial.exists_lt_one
  obtain ⟨p, rfl⟩ : ∃ p : kˣ, (p : k) = p₀ := ⟨Units.mk0 _ hp0, rfl⟩
  have hCi : valuation k ((C⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ hC1
  have hr1 : valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) < 1 := by
    simp only [Units.val_mul, map_mul]
    exact lt_of_le_of_lt ((mul_le_of_le_one_right' hCi).trans (mul_le_of_le_one_right' hCi)) hp1
  refine ⟨p * C⁻¹ * C⁻¹, hr1, fun b hb t x => ?_⟩
  have hlast : valuation k (b (Fin.last n)) < 1 := lt_of_le_of_lt (hb (Fin.last n)) hr1
  have hone : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hlast
  have hne : 1 + b (Fin.last n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hone
    exact zero_ne_one hone
  rw [shearGL_mulVec b hne x]
  have hGS : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (x + (b ⬝ᵥ x) • eLast k n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
        (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) := by
    rw [mulVec_add, mulVec_smul]
  have hd : ∀ z : Fin (n + 1) → k, b ⬝ᵥ z =
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) := by
    intro z
    rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hw : b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈
      box (n + 1) (p * C⁻¹) := by
    intro j
    change ∑ i, b i * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j ∈ cball (p * C⁻¹)
    refine Finset.sum_induction _ (· ∈ cball (p * C⁻¹)) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
    have h1 : valuation k (b i) ≤ valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) := hb i
    show valuation k (b i * _) ≤ valuation k ((p * C⁻¹ : kˣ) : k)
    rw [map_mul]
    refine (mul_le_mul' h1 (hH i j)).trans (le_of_eq ?_)
    rw [← map_mul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hdot : ∀ y ∈ box (n + 1) t,
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ y ∈
        cball (p * C⁻¹ * t) := by
    intro y hy
    refine dotProduct_mem_cball (s := t) ?_ hy
    rwa [mul_inv_cancel_right]
  have hp : valuation k (p : k) ≤ 1 := hp1.le
  constructor
  · intro h i
    have h2 : (1 + b (Fin.last n)) * (b ⬝ᵥ x) ∈ cball (p * C⁻¹ * t) := by
      rw [← dotProduct_shear, hd (x + (b ⬝ᵥ x) • eLast k n)]
      exact hdot _ h
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      have h2' : valuation k ((1 + b (Fin.last n)) * (b ⬝ᵥ x)) ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := h2
      rw [map_mul, hone, one_mul] at h2'
      exact h2'
    rw [hGS] at h
    have e : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) i =
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
          (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n)) i +
        -((b ⬝ᵥ x) * ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) := by
      simp
    rw [e]
    exact add_mem_cball (h i) (neg_mem_cball (mul_mem_cball hp h3 (hu i)))
  · intro h i
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      rw [hd x]
      exact hdot _ h
    rw [hGS]
    exact add_mem_cball (h i) (mul_mem_cball hp h3 (hu i))

end GlobalTheory.CompanionTheory.MirPair.ShearLat
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearOrbit

variable {k : Type} [Field k]

theorem shear_mul_inv (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (1 + vecMulVec (eLast k n) b) * (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b) = 1 := by
  have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
    simp [GlobalTheory.BZMir.eLast, dotProduct_single]
  have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
      b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    rw [vecMulVec_mul_vecMulVec, hd]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
    rw [← mul_one_add]
    exact inv_mul_cancel₀ hb
  rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
    one_smul, add_sub_cancel_right]

theorem shearGL_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
  have h := GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_mul_inv n b hb
  have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
    ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩
  rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dite_eq_left hu]
  exact hu.unit_spec

theorem shearGL_inv_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (((shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b :=
  Units.inv_eq_of_mul_eq_one_right (by rw [shearGL_val n b hb]; exact shear_mul_inv n b hb)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_add_ne_zero_of_mem_box (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) {b : Fin (n + 1) → k}
    (hb : b ∈ box (n + 1) r) : 1 + b (Fin.last n) ≠ 0 := by
  intro h
  have h1 : valuation k (b (Fin.last n)) ≤ valuation k (r : k) := hb (Fin.last n)
  have h2 : b (Fin.last n) = -1 := by linear_combination h
  rw [h2, Valuation.map_neg, map_one] at h1
  exact absurd hr (not_lt.mpr h1)

theorem continuous_shearGL (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) :
    Continuous fun b : (box (n + 1) r : Set (Fin (n + 1) → k)) => shearGL n b.1 := by
  have hne : ∀ b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)), 1 + b.1 (Fin.last n) ≠ 0 :=
    fun b => GlobalTheory.CompanionTheory.MirPair.ShearOrbit.one_add_ne_zero_of_mem_box n hr b.2
  have hv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      vecMulVec (GlobalTheory.BZMir.eLast k n) b.1 :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_const.add hv).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_val n b.1 (hne b)).symm
  · have hinv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
        (1 + b.1 (Fin.last n))⁻¹ :=
      (continuous_const.add ((continuous_apply _).comp continuous_subtype_val)).inv₀ hne
    exact (continuous_const.sub (hinv.smul hv)).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_inv_val n b.1 (hne b)).symm


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_levi (m : ℕ) : Continuous (levi k m) := by
  have hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m) := by
    apply continuous_matrix
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>
      first
        | exact continuous_const
        | exact continuous_id.matrix_elem _ _
        | fun_prop
  have hGL : Continuous (GlobalTheory.BZMir.glEmb k m) := Continuous.units_map _ hmat
  exact continuous_induced_rng.2 hGL

theorem isOpen_orbit_fiber {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v w : V) :
    IsOpen {p : Mir k (n + 1) | T p v = w} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hS : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have hcont : Continuous fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g) ⁻¹' {g | T g v = v} ∈ 𝓝 p := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hS.mem_nhds
    simp
  filter_upwards [hmem] with g hg
  have hg' : T (p⁻¹ * g) v = v := hg
  have hsplit : T g = T p * T (p⁻¹ * g) := by
    rw [← map_mul, mul_inv_cancel_left]
  show T g v = w
  rw [hsplit, Module.End.mul_apply, hg']
  exact hp

theorem shear_orbit_finite {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) (r : kˣ)
    (hr : valuation k (r : k) < 1) :
    ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  haveI : CompactSpace (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) r)
  have hc : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1) :=
    (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_levi (n + 1)).comp (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_shearGL n hr)
  have hlc : IsLocallyConstant fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      T (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1)) v := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro w
    exact (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.isOpen_orbit_fiber T hT v w).preimage hc
  rw [Set.image_eq_range]
  exact hlc.range_finite

end GlobalTheory.CompanionTheory.MirPair.ShearOrbit

end
end
