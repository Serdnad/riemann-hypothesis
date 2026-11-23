module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle009
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSubsetSumVanishes
public import Mathlib.Data.Fintype.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle003
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
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

section

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisSec

variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem isQuotientMap_mul [IsTopologicalGroup G] {K P : Subgroup G} (hK : IsCompact (K : Set G))
    (hP : IsClosed (P : Set G)) (hI : Iwa P K) :
    Topology.IsQuotientMap (fun x : P × K => (x.1 : G) * (x.2 : G)) :=
  _root_.UpperTheory.Reformulated.B.DYhc7.main hK hP hI

theorem sec_mul {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} (hch : IsCh Γ P c)
    {w : W} (hw : w ∈ secSp K P c ρ) {p : G} (hp : p ∈ P) (k : K) :
    sec K P c ρ (p * k) w = c p • ρ k⁻¹ w := by
  have h : ∃ k' : K, (p * (k : G)) * (k' : G)⁻¹ ∈ P := ⟨k, by simpa using hp⟩
  rw [sec, dite_eq_left h]
  obtain ⟨k0, hk0⟩ : ∃ k0 : K, k0 = h.choose := ⟨_, rfl⟩
  have h0 : p * (k : G) * (k0 : G)⁻¹ ∈ P := hk0 ▸ h.choose_spec
  rw [← hk0]
  have hr : ((k0 * k⁻¹ : K) : G) ∈ P := by
    have : ((k0 * k⁻¹ : K) : G) = (p * (k : G) * (k0 : G)⁻¹)⁻¹ * p := by simp [mul_assoc]
    rw [this]
    exact P.mul_mem (P.inv_mem h0) hp
  have hrw : c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w = w := hw _ hr
  have hcp : c p = c (p * (k : G) * (k0 : G)⁻¹) * c ((k0 * k⁻¹ : K) : G) := by
    rw [← hch.mul _ h0 _ hr]
    congr 1
    simp [mul_assoc]
  have hρ : ρ k⁻¹ = ρ k0⁻¹ * ρ (k0 * k⁻¹) := by
    rw [← map_mul]
    congr 1
    simp
  calc (c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹) w
      = c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹ (c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w) := by
        rw [hrw]; rfl
    _ = c p • ρ k⁻¹ w := by
        rw [hcp, hρ, map_smul, mul_smul]; rfl

theorem sec_continuous [IsTopologicalGroup G] {Γ K P : Subgroup G} {c : G → ℂ}
    {ρ : K →* (W →L[ℂ] W)} (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c)
    {w : W} (hw : w ∈ secSp K P c ρ) : Continuous fun g => sec K P c ρ g w := by
  refine (isQuotientMap_mul hK hpar.closed hpar.iwa).continuous_iff.mpr ?_
  have hc : Continuous fun p : P => c p := continuousOn_iff_continuous_restrict.mp hpar.ch.cont
  have he : ((fun g => sec K P c ρ g w) ∘ fun x : P × K => (x.1 : G) * (x.2 : G))
      = fun x : P × K => c x.1 • ρ x.2⁻¹ w := by
    funext x
    exact sec_mul hpar.ch hw x.1.2 x.2
  rw [he]
  have h2 : Continuous fun k : K => ρ k⁻¹ w :=
    (hρ.comp continuous_inv).clm_apply continuous_const
  exact (hc.comp continuous_fst).smul (h2.comp continuous_snd)

theorem sec_bound {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)}
    (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c) :
    ∃ M : ℝ, ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hρ).isBounded.exists_norm_le
  refine ⟨M, fun g w => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hpar.iwa g
  have h : ∃ k' : K, (p * k) * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [sec, dite_eq_left h, ContinuousLinearMap.smul_apply, norm_smul, hpar.ch.norm _ h.choose_spec,
    one_mul]
  exact ((ρ _).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hM _ ⟨_, rfl⟩) (norm_nonneg _))

theorem secLaw : SecLaw := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P c hpar
  exact ⟨fun w hw p hp k => sec_mul hpar.ch hw hp k,
    fun w hw => sec_continuous hK hρ hpar hw, sec_bound hK hρ hpar⟩

end GlobalTheory.CompanionTheory.RgEisSec
end
end

section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def pt (x y : ℝ × ℝ) : ℂ × ℂ := (⟨x.1, y.1⟩, ⟨x.2, y.2⟩)

def dot (l : ℂ × ℂ) (t : ℝ × ℝ) : ℂ := l.1 * t.1 + l.2 * t.2

def rdot (x t : ℝ × ℝ) : ℝ := x.1 * t.1 + x.2 * t.2

def phi (G : ℂ × ℂ → X) (x t : ℝ × ℝ) : X :=
  ∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)

def inv (φ : ℝ × ℝ → X) (l : ℂ × ℂ) : X :=
  (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t

def gauss (F : ℂ × ℂ → X) (l : ℂ × ℂ) : X := Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F l

structure GaussTube (G : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol G (tube Ω)
  cont : ContinuousOn G (tube Ω)
  decay : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C,
    ‖G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))

def ExpDecay {T : Type} [TopologicalSpace T] (φ : ℝ × ℝ → T → X) : Prop :=
  ∀ (x₀ : ℝ × ℝ) (g : T), ∃ ε : ℝ, 0 < ε ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - x₀.1| ≤ ε → |x.2 - x₀.2| ≤ ε →
    ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))

theorem norm_exp_sq (l : ℂ × ℂ) : ‖Complex.exp (l.1 ^ 2 + l.2 ^ 2)‖ =
    Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [sq]
  ring

theorem gauss_bound {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω C : Set (ℝ × ℝ)} (h : TubeGood F Ω)
    (hC : C ⊆ Ω) (hc : IsCompact C) (g : T) : ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ l ∈ tube C,
      ‖gauss (F · g') l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  obtain ⟨U, hU, M, hM⟩ := h.bdd C hC hc g
  obtain ⟨B, hB⟩ := (hc.image (f := fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2) (by fun_prop)).bddAbove
  refine ⟨U, hU, Real.exp B * |M|, fun g' hg' l hl => ?_⟩
  have h1 : l.1.re ^ 2 + l.2.re ^ 2 ≤ B := hB ⟨(l.1.re, l.2.re), hl, rfl⟩
  have h2 : ‖F l g'‖ ≤ |M| := (hM l hl g' hg').trans (le_abs_self M)
  simp only [gauss]
  rw [norm_smul, norm_exp_sq]
  have h3 : Real.exp (l.1.re ^ 2 + l.2.re ^ 2) ≤ Real.exp B := Real.exp_le_exp.2 h1
  have h4 := Real.exp_pos (-(l.1.im ^ 2 + l.2.im ^ 2))
  calc _ = Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * ‖F l g'‖ * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring
    _ ≤ Real.exp B * |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by gcongr

theorem gaussTube_of_tubeGood {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (h : TubeGood F Ω) (g : T) : GaussTube (gauss (F · g)) Ω := by
  refine ⟨?_, ?_, ?_⟩
  · intro p v
    have h1 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).1 ^ 2 + (p + τ • v).2 ^ 2) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      fun_prop
    exact h1.differentiableOn.smul (h.hol g p v)
  · have h1 : ContinuousOn (fun l : ℂ × ℂ => F l g) (tube Ω) :=
      h.cont.comp (f := fun l : ℂ × ℂ => (l, g)) (by fun_prop) fun l hl => ⟨hl, trivial⟩
    exact ContinuousOn.smul (by fun_prop) h1
  · intro C hC hc
    obtain ⟨U, hU, M, hM⟩ := gauss_bound h hC hc g
    exact ⟨M, fun l hl => hM g (mem_of_mem_nhds hU) l hl⟩

end GlobalTheory.CompanionTheory.TubeFourier
end
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeSign

theorem sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ x ∈ s, f x ≠ 0) :
    0 < (-1 : ℝ) ^ (s.filter fun x => f x < 0).card * ∏ x ∈ s, f x := by
  have e : (-1 : ℝ) ^ (s.filter fun x => f x < 0).card
      = ∏ x ∈ s, (if f x < 0 then (-1 : ℝ) else 1) := by
    rw [Finset.prod_ite]; simp
  rw [e, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro x hx
  split_ifs with hneg
  · linarith
  · have : 0 < f x := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm (h x hx))
    linarith

theorem sign_div {a b P Q : ℝ} (hP : 0 < a * P) (hQ : 0 < b * Q) : 0 < a * b * (P / Q) := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hQ
  have e : a * b * (P / Q) = (a * P) * (b * Q) / Q ^ 2 := by
    field_simp
  rw [e]
  exact div_pos (mul_pos hP hQ) (by positivity)

theorem above_eq {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (r : ℝ) :
    above d d' r = (univ.filter fun k => r < d k).card + (univ.filter fun j => r < d' j).card := by
  unfold above
  simp only [Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  congr!

theorem pfSign {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hinj : Function.Injective (Sum.elim d d')) :
    (∀ i, 0 < (-1 : ℝ) ^ above d d' (d i) * pfD d d' i) ∧
      ∀ j, 0 < (-1 : ℝ) ^ above d d' (d' j) * pfR d d' j := by
  have hd : ∀ {i k}, k ≠ i → d i - d k ≠ 0 := by
    intro i k hk h
    apply hk
    have := hinj (a₁ := Sum.inl k) (a₂ := Sum.inl i) (by simpa using (sub_eq_zero.mp h).symm)
    simpa using this
  have hd' : ∀ {j k}, k ≠ j → d' j - d' k ≠ 0 := by
    intro j k hk h
    apply hk
    have := hinj (a₁ := Sum.inr k) (a₂ := Sum.inr j) (by simpa using (sub_eq_zero.mp h).symm)
    simpa using this
  have hx : ∀ i j, d i - d' j ≠ 0 := by
    intro i j h
    have := hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simpa using sub_eq_zero.mp h)
    simp at this
  have hy : ∀ j i, d' j - d i ≠ 0 := by
    intro j i h
    exact hx i j (by linarith)
  constructor
  · intro i
    have h1 := sign_prod (univ.erase i) (fun k => d i - d k)
      (fun k hk => hd (Finset.ne_of_mem_erase hk))
    have h2 := sign_prod (univ : Finset (Fin m)) (fun j => d i - d' j) (fun j _ => hx i j)
    have e1 : ((univ.erase i).filter fun k => d i - d k < 0) = univ.filter fun k => d i < d k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, sub_neg]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact lt_irrefl _ h
    have e2 : (univ.filter fun j => d i - d' j < 0) = univ.filter fun j => d i < d' j := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
    rw [e1] at h1
    rw [e2] at h2
    rw [above_eq, pow_add]
    exact sign_div h1 h2
  · intro j
    have h1 := sign_prod (univ : Finset (Fin (m + 1))) (fun i => d' j - d i) (fun i _ => hy j i)
    have h2 := sign_prod (univ.erase j) (fun k => d' j - d' k)
      (fun k hk => hd' (Finset.ne_of_mem_erase hk))
    have e1 : (univ.filter fun i => d' j - d i < 0) = univ.filter fun i => d' j < d i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
    have e2 : ((univ.erase j).filter fun k => d' j - d' k < 0)
        = univ.filter fun k => d' j < d' k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, sub_neg]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact lt_irrefl _ h
    rw [e1] at h1
    rw [e2] at h2
    rw [above_eq, pow_add]
    exact sign_div h1 h2

end GlobalTheory.CompanionTheory.RgHeSign
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe.Frame

open Polynomial

theorem degree_sub_lt_of_nextCoeff_eq {p q : ℝ[X]} {m : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m + 1) (hqd : q.natDegree = m + 1) (hn : p.nextCoeff = q.nextCoeff) :
    (p - q).degree < (m : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_sub]
  rcases hk.eq_or_lt with rfl | hk'
  · have h1 : p.nextCoeff = p.coeff m := by
      rw [nextCoeff_of_natDegree_pos (by omega), hpd]; rfl
    have h2 : q.nextCoeff = q.coeff m := by
      rw [nextCoeff_of_natDegree_pos (by omega), hqd]; rfl
    rw [← h1, ← h2, hn, sub_self]
  · rcases (Nat.succ_le_of_lt hk').eq_or_lt with rfl | hk''
    · have h1 := hp.coeff_natDegree
      have h2 := hq.coeff_natDegree
      rw [hpd] at h1
      rw [hqd] at h2
      rw [h1, h2, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
        sub_zero]

theorem prod_eq_partial_fraction {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hd' : Function.Injective d') :
    (∏ i, (X - C (d i))) = (X - C (pfX d d')) * (∏ j, (X - C (d' j))) +
      ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) := by
  have hPm : (∏ i, (X - C (d i)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hQm : (∏ j, (X - C (d' j)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPd : (∏ i, (X - C (d i)) : ℝ[X]).natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hRm : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic := (monic_X_sub_C _).mul hQm
  have hRd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m + 1 := by
    rw [(monic_X_sub_C _).natDegree_mul hQm, hQd, natDegree_X_sub_C]; omega
  have hn : (∏ i, (X - C (d i)) : ℝ[X]).nextCoeff =
      ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).nextCoeff := by
    rw [(monic_X_sub_C _).nextCoeff_mul hQm, prod_X_sub_C_nextCoeff, prod_X_sub_C_nextCoeff,
      nextCoeff_X_sub_C, pfX]
    ring
  have hD := degree_sub_lt_of_nextCoeff_eq hPm hRm hPd hRd hn
  have hS : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < (m : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul]
    have hL : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).natDegree < n := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
      have hj : (univ.erase j).card + 1 = m := by
        rw [Finset.card_erase_of_mem (mem_univ j)]
        have : 0 < m := j.pos
        simp only [card_univ, Fintype.card_fin]
        omega
      simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hL, mul_zero]
  have hcard : (#(univ : Finset (Fin m)) : ℕ) = m := by simp
  have key := Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := (univ : Finset (Fin m)))
    (v := d') (f := (∏ i, (X - C (d i))) - (X - C (pfX d d')) * ∏ j, (X - C (d' j)))
    (g := ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)))
    hd'.injOn (by rw [hcard]; exact hD) (by rw [hcard]; exact hS) (by
      intro j _
      have hne : ∏ k ∈ univ.erase j, (d' j - d' k) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr fun h => ?_
        exact (Finset.mem_erase.mp hk).1 (hd' h).symm
      have hQ0 : (∏ l, (d' j - d' l)) = 0 :=
        Finset.prod_eq_zero (mem_univ j) (sub_self _)
      have hterm : ∀ l ∈ (univ : Finset (Fin m)), l ≠ j →
          pfR d d' l * ∏ k ∈ univ.erase l, (d' j - d' k) = 0 := by
        intro l _ hl
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl.symm, mem_univ j⟩) (sub_self _), mul_zero]
      simp only [eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finsetSum]
      rw [hQ0, mul_zero, sub_zero, Finset.sum_eq_single_of_mem j (mem_univ j) hterm, pfR,
        div_mul_cancel₀ _ hne])
  rw [← key]
  ring

theorem pfZero {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hinj : Function.Injective (Sum.elim d d')) (i : Fin (m + 1)) :
    d i - pfX d d' + ∑ j, pfR d d' j / (d i - d' j) = 0 := by
  have hd' : Function.Injective d' := fun a b h =>
    Sum.inr_injective (hinj (by simpa using h))
  have hne : ∀ j, d i - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h => by
    simpa using hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simpa using h)
  have hQ : ∏ j, (d i - d' j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  have h := congrArg (eval (d i)) (prod_eq_partial_fraction d d' hd')
  simp only [eval_add, eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finsetSum] at h
  rw [Finset.prod_eq_zero (mem_univ i) (sub_self _)] at h
  have hsum : ∀ j, pfR d d' j * ∏ k ∈ univ.erase j, (d i - d' k) =
      (pfR d d' j / (d i - d' j)) * ∏ k, (d i - d' k) := by
    intro j
    rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
    field_simp [hne j]
  simp only [hsum, ← Finset.sum_mul] at h
  rw [← add_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_right hQ

end GlobalTheory.CompanionTheory.RgHe.Frame
end

section

open Polynomial

theorem _root_.GlobalTheory.T.tensor_sum_annihilator : ∀ {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ), ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KillSum.sum_killed | exact GlobalTheory.CompanionTheory.KillSum.sum_killed | (intros; apply GlobalTheory.CompanionTheory.KillSum.sum_killed <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.product_subset_sum_vanishes : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ) (m : Multiset ℂ) (A B : R[X]), 0 < r → A.Monic → B.Monic → A.natDegree = r →
  A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod →
  ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | exact GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | (intros; apply GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.coset_sum_translate_invariant : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  first | exact @GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal | exact GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal | (intros; apply GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal <;> assumption)
end

section


theorem _root_.GlobalTheory.T.multiplicative_character_on_cone : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char | exact GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char | (intros; apply GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char <;> assumption)
end

section


theorem _root_.GlobalTheory.T.antitone_weighted_sum_zero : ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 → (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) → ∀ i, e i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg | exact GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg | (intros; apply GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg <;> assumption)
end

section


theorem _root_.GlobalTheory.T.prod_le_rev_eq_prod_ge : ∀ {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h), ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a) = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  first | exact @GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev | exact GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev | (intros; apply GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_support_product_quotient : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite → (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite → (∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) → (∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) → (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  first | exact @GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | exact GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | (intros; apply GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite <;> assumption)
end
