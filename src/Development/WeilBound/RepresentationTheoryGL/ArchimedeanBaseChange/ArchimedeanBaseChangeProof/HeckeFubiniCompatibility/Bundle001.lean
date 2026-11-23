module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG.ReproL

theorem norm_cosh_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Complex.cosh z - 1‖ ≤ 2 * ‖z‖ := by
  have h1 := Complex.norm_exp_sub_one_le hz
  have h2 := Complex.norm_exp_sub_one_le (x := -z) (by rwa [norm_neg])
  rw [norm_neg] at h2
  have e : Complex.cosh z - 1 = ((Complex.exp z - 1) + (Complex.exp (-z) - 1)) / 2 := by
    rw [show Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 from rfl]; ring
  rw [e, norm_div]
  have h3 := norm_add_le (Complex.exp z - 1) (Complex.exp (-z) - 1)
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4]
  linarith

theorem continuous_cas (N : ℕ) : Continuous fun χ : Inf N => cas χ := by
  have hA : ∀ f : Inf N → Fin N → ℂ, Continuous f → Continuous fun χ => Formalism.REAL.Amat (f χ) := by
    intro f hf
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply a).comp hf
    · exact continuous_const
    · exact continuous_const
  have hg : ∀ s : Bool, Continuous fun χ : Inf N => GlobalTheory.Dec.gelfVal (χ s) 2 := by
    intro s
    unfold GlobalTheory.Dec.gelfVal
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    have hf : Continuous fun χ : Inf N => fun c : Fin N => χ s c + ((N : ℂ) - 1) / 2 :=
      continuous_pi fun c => (continuous_apply_apply s c).add continuous_const
    exact ((hA _ hf).pow 2).matrix_elem a b
  unfold cas
  exact continuous_const.mul ((hg true).add (hg false))

theorem exists_bump (N : ℕ) (R : ℝ) : ∃ (g : ℝ → ℝ) (T : ℝ), 0 < T ∧ IsBump g T ∧
    ∀ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) → 1 / 2 ≤ ‖coshT g (cas χ)‖ := by
  have hS : IsCompact {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} := by
    have e : {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} =
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) R := by
      ext χ; simp [Set.mem_pi]
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (continuous_cas N).continuousOn
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set s := Real.sqrt C' with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set T : ℝ := 1 / (4 * (s + 1)) with hT
  have hT0 : 0 < T := by positivity
  have hTs : T * s ≤ 1 / 4 := by
    rw [hT, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  let f : ContDiffBump (0 : ℝ) := ⟨T / 2, T, by positivity, by linarith⟩
  set g : ℝ → ℝ := f.normed volume with hg
  have hsupp : ∀ t, g t ≠ 0 → |t| < T := by
    intro t ht
    have : t ∈ Function.support g := ht
    rw [hg, ContDiffBump.support_normed_eq] at this
    simpa [Metric.mem_ball, Real.dist_eq] using this
  refine ⟨g, T, hT0, ⟨ContDiffBump.contDiff_normed f, fun t => ?_, fun t ht => ?_⟩, ?_⟩
  · have := ContDiffBump.normed_neg f (μ := volume) t
    simpa [hg] using this
  · by_contra h
    exact absurd (hsupp t h) (not_lt.2 ht.le)
  intro χ hχ
  set c := cas χ with hc
  have hcC : ‖c‖ ≤ C' := (hC χ hχ).trans (le_max_left _ _)
  have hroot : ‖c ^ (1 / 2 : ℂ)‖ ≤ s := by
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, hs]
    exact Real.sqrt_le_sqrt hcC
  have hgc : Continuous g := (ContDiffBump.contDiff_normed f (n := 0)).continuous
  have hgcs : HasCompactSupport g := ContDiffBump.hasCompactSupport_normed f
  have hgC : HasCompactSupport fun t => (g t : ℂ) := hgcs.comp_left Complex.ofReal_zero
  have hcont1 : Continuous fun t : ℝ => Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)
  have hi1 : Integrable fun t : ℝ => (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    ((Complex.continuous_ofReal.comp hgc).mul hcont1).integrable_of_hasCompactSupport (hgC.mul_right)
  have hi2 : Integrable fun t : ℝ => (g t : ℂ) :=
    (Complex.continuous_ofReal.comp hgc).integrable_of_hasCompactSupport hgC
  have hone : ∫ t, (g t : ℂ) = 1 := by
    rw [integral_complex_ofReal, hg, ContDiffBump.integral_normed]; simp
  have h3 : ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) =
      (∫ t, (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ))) - ∫ t, (g t : ℂ) := by
    rw [← integral_sub hi1 hi2]; congr 1; funext t; ring
  have hdiff : coshT g c - 1 = ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) := by
    rw [h3, hone]; rfl
  have hbound : ∀ t, ‖(g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ g t * (1 / 2) := by
    intro t
    by_cases h0 : g t = 0
    · simp [h0]
    have ht := hsupp t h0
    have hz : ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |t| * ‖c ^ (1 / 2 : ℂ)‖ ≤ T * s := mul_le_mul ht.le hroot (norm_nonneg _) hT0.le
        _ ≤ 1 / 4 := hTs
    have hgt : 0 ≤ g t := ContDiffBump.nonneg_normed f t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgt]
    refine mul_le_mul_of_nonneg_left ?_ hgt
    calc ‖Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1‖ ≤ 2 * ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ :=
          norm_cosh_sub_one_le (hz.trans (by norm_num))
      _ ≤ 1 / 2 := by linarith
  have hle : ‖coshT g c - 1‖ ≤ 1 / 2 := by
    rw [hdiff]
    calc ‖∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ ∫ t, g t * (1 / 2) :=
          norm_integral_le_of_norm_le ((hgc.mul continuous_const).integrable_of_hasCompactSupport hgcs.mul_right)
            (Filter.Eventually.of_forall hbound)
      _ = 1 / 2 := by rw [integral_mul_const, hg, ContDiffBump.integral_normed]; ring
  have := norm_sub_norm_le (1 : ℂ) (1 - coshT g c)
  rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
  linarith

theorem exists_enum {N : ℕ} (m : Multiset ℂ) (h : Multiset.card m = N) :
    ∃ e : Fin N → ℂ, Multiset.map e Finset.univ.val = m := by
  subst h
  refine ⟨fun i => m.toList.get (Fin.cast (by simp) i), ?_⟩
  rw [Fin.univ_val_map]
  have e : List.ofFn (fun i : Fin (Multiset.card m) => m.toList.get (Fin.cast (by simp) i)) = m.toList :=
    List.ext_get (by simp) (by simp)
  rw [e, Multiset.coe_toList]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_chi (hB : Bridge.BridgeSt) (R : ℝ) (v : InfinitePlace E) (φ : Sm E N)
    (hR : PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ})) :
    ∃ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) ∧ ∀ g : GA E N, IsEig χ (Bridge.along v g φ.1) := by
  obtain ⟨m1, h1, b1⟩ := hR v.embedding
  obtain ⟨m2, h2, b2⟩ := hR (ComplexEmbedding.conjugate v.embedding)
  obtain ⟨e1, he1⟩ := exists_enum m1 h1.1
  obtain ⟨e2, he2⟩ := exists_enum m2 h2.1
  refine ⟨fun s => if s then e1 else e2, ?_, ?_⟩
  · intro s i
    cases s
    · exact b2 _ (he2 ▸ Multiset.mem_map_of_mem e2 (Finset.mem_univ_val i))
    · exact b1 _ (he1 ▸ Multiset.mem_map_of_mem e1 (Finset.mem_univ_val i))
  · intro g
    have key := (hB E N (Submodule.span ℂ {φ}) v (fun s => if s then e1 else e2)).2
      ⟨by simpa [he1] using h1, by simpa [he2] using h2⟩
    exact key φ (Submodule.mem_span_singleton_self φ) g

end PositivityTheory.Rg.BcB.CG.ReproL
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)

namespace PositivityTheory.Rg.BcB.CG

abbrev Ix {n : ℕ} (M : KMod n) : Type := Fin (Module.finrank ℂ M.V)

def ent {n : ℕ} (M : KMod n) (A : M.V →L[ℂ] M.V) (i j : Ix M) : ℂ :=
  inner ℂ (stdOrthonormalBasis ℂ M.V i) (A (stdOrthonormalBasis ℂ M.V j))

theorem ent_zero {n : ℕ} (M : KMod n) (i j : Ix M) : ent M 0 i j = 0 := by simp [ent]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

def gInf (v : InfinitePlace E) : GA E n →* G n := GeneralLinearGroup.map (cV v)

def gFin : GA E n →* GL (Fin n) (Af E) := GeneralLinearGroup.map (pFin E)

def hFin (g : H E a b) : Hf E a b := (gFin g.1, gFin g.2)

abbrev Mods (E : Type) [Field E] (n : ℕ) : Type 1 := InfinitePlace E → KMod n

abbrev Kers (M : Mods E n) : Type := ∀ v, Mat n → ((M v).V →L[ℂ] (M v).V)

abbrev Ops (M : Mods E n) : Type := ∀ v, (M v).V →L[ℂ] (M v).V

abbrev IxA (M : Mods E n) : Type := ∀ v, Ix (M v)

abbrev Io (Ma : Mods E a) (Mb : Mods E b) (κ : Type) : Type := (IxA Ma × IxA Mb) × κ

def entA {M : Mods E n} (k : Kers M) (i j : IxA M) (g : GA E n) : ℂ := ∏ v, ent (M v) (k v (gInf v g).val) (i v) (j v)

def tens {Ma : Mods E a} {Mb : Mods E b} {κ : Type} (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) :
    Matrix (Io Ma Mb κ) (Io Ma Mb κ) (H E a b → ℂ) :=
  fun i j g => entA ka i.1.1 j.1.1 g.1 * entA kb i.1.2 j.1.2 g.2 * ψ i.2 j.2 (hFin g)

def opM {Ma : Mods E a} {Mb : Mods E b} {κ : Type} (Ta : Ops Ma) (Tb : Ops Mb) (N : Matrix κ κ ℂ) :
    Matrix (Io Ma Mb κ) (Io Ma Mb κ) ℂ :=
  fun i j => (∏ v, ent (Ma v) (Ta v) (i.1.1 v) (j.1.1 v)) * (∏ v, ent (Mb v) (Tb v) (i.1.2 v) (j.1.2 v)) * N i.2 j.2

def IsMults [MeasurableSpace (G n)] (μ : Measure (G n)) {M : Mods E n} (k : Kers M) (val : InfinitePlace E → Inf n → ℂ)
    (T : ℝ) : Prop := ∀ v, IsMult μ (M v) (k v) (val v) T

def valA (val : InfinitePlace E → Inf n → ℂ) (χ : InfinitePlace E → Inf n) : ℂ := ∏ v, val v (χ v)

def IsFinM {κ : Type} (ψ : Matrix κ κ (Hf E a b → ℂ)) : Prop := ∀ x y, Continuous (ψ x y) ∧ HasCompactSupport (ψ x y)

def mulF {κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)) : Matrix κ κ (Hf E a b → ℂ) :=
  fun x y g => ∑ z, ∫ h, ψ x z h * ψ' z y (h⁻¹ * g) ∂ν

def adjF {κ : Type} (ψ : Matrix κ κ (Hf E a b → ℂ)) : Matrix κ κ (Hf E a b → ℂ) :=
  fun x y g => starRingEnd ℂ (ψ y x g⁻¹)

def convF {A κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : A × κ → H E a b → ℂ) : A × κ → H E a b → ℂ :=
  fun i x => ∑ z, ∫ h, ψ i.2 z h * f (i.1, z) (x * finH h) ∂ν

def adjK {M : Mods E n} (k : Kers M) : Kers M := fun v y =>
  haveI := FiniteDimensional.complete ℂ (M v).V
  ContinuousLinearMap.adjoint (k v y⁻¹)

def convK [MeasurableSpace (G n)] (μ : Measure (G n)) {M : Mods E n} (k k' : Kers M) : Kers M :=
  fun v => PositivityTheory.RgBcC.conv μ (M v) (k v) (k' v)

def Compat (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)]
    (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) : Prop :=
  letI := borelH E a b
  ∀ (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ),
    (∀ v, Continuous (fa v) ∧ HasCompactSupport (fa v)) → (∀ v, Continuous (fb v) ∧ HasCompactSupport (fb v)) →
    Continuous ψ → HasCompactSupport ψ →
    ∫ g, (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g) ∂D.μ =
      (∏ v, ∫ y, fa v y ∂μa) * (∏ v, ∫ y, fb v y ∂μb) * ∫ h, ψ h ∂ν

def VCClause [MeasurableSpace (G n)] (f : G n → ℂ) : Prop :=
  ∀ (d : G n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → W₁ ≠ ⊥ →
    (fun v => d.val *ᵥ v) '' PositivityTheory.RgBcC.perp W₂ = W₁ → (fun v => d.val *ᵥ v) '' PositivityTheory.RgBcC.perp W₁ = W₂ →
    ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ → ∀ (ν : Measure N) [ν.IsHaarMeasure],
      ∫ u : N, f (u * d) ∂ν = 0

def mOf (χ : InfinitePlace E → Inf n) (τ : E →+* ℂ) : Multiset ℂ := by
  classical
  exact Multiset.map (χ (InfinitePlace.mk τ) (decide (τ = (InfinitePlace.mk τ).embedding))) Finset.univ.val

end PositivityTheory.Rg.BcB.CG

end
end
