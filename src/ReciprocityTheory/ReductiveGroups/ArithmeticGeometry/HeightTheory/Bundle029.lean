module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import ReciprocityTheory.SemistableReduction.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CoeffPsiBNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FZEqConstMulIrreduciblePow

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

private theorem hintIS_log_nrm_of_mem_graded (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ} {G : WT}
    {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0) (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    (hI : d.HintIS c sg (fun P => Real.log (d.nrm c G e P))) :
    d.HintIS c sg (fun P => Real.log (d.nrm c G f P)) := by
  have h1 := d.hint_intNorm hd h c sg (ratio (Ω := Ω c) f e) (d.hint_ratio_ne hd he he0 hf hf0)
  have h2 := d.hintIS_lin hd h (φ₁ := fun P => Real.log ‖P (ratio (Ω := Ω c) f e)‖) h1 hI 1 1 0
  refine d.hintIS_congr hd h (ψ := fun P => Real.log (d.nrm c G f P)) h2 ?_
  intro P _
  try dsimp only
  rw [d.hint_log_line hd he he0 hf hf0 P]
  ring

theorem int_Nsg (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    (∀ (G : WT) (f : A c), G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      f ∈ 𝒜 c G → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G f P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) ∧
    (∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c d.wL f P / d.be c P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) := by
  obtain ⟨h_et, h_w, h_ta1, ⟨e, he, he0, h_e⟩, h_ta2⟩ := d.hint_chain hd h hI2be c sg
  have hL : ∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      d.HintIS c sg (fun P => Real.log (d.nrm c d.wL f P)) :=
    fun f hf hf0 => hintIS_log_nrm_of_mem_graded d hd h (hd.w_mem (d.jc c) c) (hd.w_base c) hf hf0 h_w
  refine ⟨fun G f hG hf hf0 => ?_, fun f hf hf0 => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
    rcases hG with rfl | rfl | rfl | rfl | rfl
    · exact hL f hf hf0
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.et_mem c) (hd.et_ne c) hf hf0 h_et
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.firstSectionMem c) (hd.firstSectionNeZero c) hf hf0 h_ta1
    · exact hintIS_log_nrm_of_mem_graded d hd h he he0 hf hf0 h_e
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.secondSectionMem c) (hd.secondSectionNeZero c) hf hf0 h_ta2
  · have h3 := d.hintIS_lin hd h (hL f hf hf0) h_w 1 (-1) 0
    have h4 := d.hintIS_lin hd h (φ₂ := fun P => Real.log ‖d.hintU c P‖) h3
      (d.hint_intU hd h c sg) 1 (-1) 0
    refine d.hintIS_congr hd h (ψ := fun P => Real.log (d.nrm c d.wL f P / d.be c P)) h4 ?_
    intro P _
    try dsimp only
    have hpos := hd.nrm_pos c P hf hf0
    have hw := hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c)
    have hU := d.hint_one_le_U hd c P
    have hbe : d.be c P ≠ 0 := by
      rw [d.hint_be_eq hd c P]
      exact (mul_pos hw (lt_of_lt_of_le one_pos hU)).ne'
    rw [Real.log_div hpos.ne' hbe, d.hint_log_be hd c P]
    ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem irreducible_factor_structure (hd : d.AxH 𝒜) (h : d.S1) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 (F c)) :
    ∃ (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (κ : K)
      (a m deF : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ m * deF ≤ d.delc c ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d.delc c) ∧
      bilinearSubstitution (F c) = MvPolynomial.C κ * MvPolynomial.X (Sum.inr 0) ^ a * F1 ^ m ∧
      d.linearSubstitution c (bilinearSubstitution (F c)) = 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := by

  obtain ⟨F0, κ0, m0, hκ0, hm0, hirr0, hFeq, hker⟩ := d.fZ_eq_const_mul_irreducible_pow hd h c (F c) (hF c) hpos
  obtain ⟨F', hF', -, hmh', -⟩ := d.componentForm_properties hd h c
  have hFF : F c = F' := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) ((hF c).trans hF'.symm)
  have hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := hFF ▸ hmh'
  have hmh1 : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (MvPolynomial.C κ0 * F0 ^ m0) := by
    rw [← hFeq]; exact hmh
  obtain ⟨d0, hd0, hmh0⟩ :=
    MHF.isMH_of_pow (Nat.succ_pos _) F0 κ0 m0 (d.delc c) hm0 hκ0 hirr0.ne_zero hmh1
  obtain ⟨a0, F1, deF, hG0, hirr1, hxh, hdeF, hU⟩ := d.substitution_split_irreducible hd c F0 hirr0 d0 hmh0 hker
  have hg : bilinearSubstitution (F c) = MvPolynomial.C κ0 * bilinearSubstitution F0 ^ m0 := by
    rw [hFeq]; simp only [bilinearSubstitution, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  refine ⟨F1, κ0, a0 * m0, m0, deF, hκ0, hm0, ?_, hirr1, hxh, ?_, ?_, ?_, hmh⟩
  · calc m0 * deF ≤ m0 * d0 := Nat.mul_le_mul_left _ hdeF
      _ = d.delc c := hd0
  · intro s hs
    refine (hU s hs).trans (Nat.mul_le_mul_left _ ?_)
    calc d0 ≤ m0 * d0 := Nat.le_mul_of_pos_left _ hm0
      _ = d.delc c := hd0
  · rw [hg, hG0, mul_pow, pow_mul]; ring
  · rw [hg, map_mul, map_pow, d.substitution_vanishes_of_relation hd c F0 ((hker F0).2 dvd_rfl), zero_pow (by omega), mul_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
