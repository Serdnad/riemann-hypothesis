module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle099
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.DistLa

variable {D : D7} {N N' : ℕ}

theorem La_map (T : Tor D) (f : VC D N N' →ₗ[ℂ] VC D N N')
    (g : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E)
    (hfg : ∀ A, f (embV D T A) = embV D T (g A)) {L M : Lat D N} {L' M' : Lat D N'}
    (hg : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L, A.mulVec x ∈ L') → ∀ x ∈ M, (g A).mulVec x ∈ M')
    {z : VC D N N'} (hz : z ∈ La D T L L') : f z ∈ La D T M M' := by
  have h1 : ∀ A ∈ homL D L L', g A ∈ homL D M M' := by
    intro A hA
    have : homL D L L' ≤ (homL D M M').comap (g.restrictScalars (𝓞 D.host.E)) :=
      Submodule.span_le.2 fun B hB => Submodule.subset_span (hg B hB)
    exact this hA
  have h2 : ∀ A ∈ YYl D L L', g A ∈ YYl D M M' := by
    intro A hA
    have : YYl D L L' ≤ (YYl D M M').comap (g.restrictScalars (𝓞 D.host.E)) := by
      refine Submodule.span_le.2 ?_
      rintro B ⟨a, ha, C, hC, rfl⟩
      exact Submodule.subset_span ⟨a, ha, g C, h1 C hC, map_smul g a C⟩
    exact this hA
  have h3 : La D T L L' ≤ (La D T M M').comap f.toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, g A, h2 A hA, ?_⟩
    show f (w • embV D T A) = _
    rw [map_smul, hfg]
  exact h3 hz

def lft (P : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ i j => ∑ k, embT D τ (P i k) * z τ k j
  map_add' x y := by
    funext τ i j; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

def rgt (P : Matrix (Fin N) (Fin N) D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ i j => ∑ k, z τ i k * embT D τ (P k j)
  map_add' x y := by
    funext τ i j; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem lft_add (P : Matrix (Fin N') (Fin N') D.host.E) (z : VC D N N') : lft P z + lft (1 - P) z = z := by
  funext τ i j
  show ∑ k, embT D τ (P i k) * z τ k j + ∑ k, embT D τ ((1 - P) i k) * z τ k j = z τ i j
  rw [← Finset.sum_add_distrib]
  simp only [← add_mul, ← map_add (f := _), Matrix.sub_apply, add_sub_cancel, Matrix.one_apply]
  simp [apply_ite]

theorem rgt_add (P : Matrix (Fin N) (Fin N) D.host.E) (z : VC D N N') : rgt P z + rgt (1 - P) z = z := by
  funext τ i j
  show ∑ k, z τ i k * embT D τ (P k j) + ∑ k, z τ i k * embT D τ ((1 - P) k j) = z τ i j
  rw [← Finset.sum_add_distrib]
  simp only [← mul_add, ← map_add (f := _), Matrix.sub_apply, add_sub_cancel, Matrix.one_apply]
  simp [apply_ite]

theorem lft_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N') (Fin N') D.host.E) {L : Lat D N}
    {L' M' : Lat D N'} (hP : ∀ v ∈ L', P.mulVec v ∈ M') {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') :
    lft P z ∈ La D (tor0 D cc δ) L M' := by
  refine La_map _ (lft P)
    { toFun := fun A => P * A, map_add' := fun A B => Matrix.mul_add P A B,
      map_smul' := fun c A => Matrix.mul_smul P c A } ?_ ?_ hz
  · intro A
    funext τ i j
    show ∑ k, embT D τ (P i k) * embT D τ (A k j) = embT D τ ((P * A) i j)

    simp only [Matrix.mul_apply, map_sum, map_mul]
  · intro A hA x hx
    show (P * A).mulVec x ∈ M'
    rw [← Matrix.mulVec_mulVec]
    exact hP _ (hA x hx)

theorem rgt_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N) (Fin N) D.host.E) {L M : Lat D N}
    {L' : Lat D N'} (hP : ∀ v ∈ M, P.mulVec v ∈ L) {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') :
    rgt P z ∈ La D (tor0 D cc δ) M L' := by
  refine La_map _ (rgt P)
    { toFun := fun A => A * P, map_add' := fun A B => Matrix.add_mul A B P,
      map_smul' := fun c A => Matrix.smul_mul c A P } ?_ ?_ hz
  · intro A
    funext τ i j
    show ∑ k, embT D τ (A i k) * embT D τ (P k j) = embT D τ ((A * P) i j)

    simp only [Matrix.mul_apply, map_sum, map_mul]
  · intro A hA x hx
    show (A * P).mulVec x ∈ L'
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hP x hx)

theorem one_sub_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    (1 - P).mulVec v = v - P.mulVec v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem bet_proj {n : ℕ} {L₁ L₂ L₃ : Lat D n} (hb : Bet D L₁ L₂ L₃) {P : Matrix (Fin n) (Fin n) D.host.E}
    (h1 : ∀ v ∈ L₁ ⊔ L₃, P.mulVec v ∈ L₁) (h2 : ∀ v ∈ L₃, P.mulVec v ∈ L₃)
    (h3 : ∀ v ∈ L₁, v - P.mulVec v ∈ L₃) (v : Fin n → D.host.E) (hv : v ∈ L₂) :
    P.mulVec v ∈ L₁ ∧ P.mulVec v ∈ L₂ ∧ v - P.mulVec v ∈ L₃ := by
  obtain ⟨a, ⟨ha1, ha2⟩, b, ⟨hb2, hb3⟩, rfl⟩ := Submodule.mem_sup.1 (hb.1 hv)
  have pa := h1 a (Submodule.mem_sup_left ha1)
  have pb := h1 b (Submodule.mem_sup_right hb3)
  rw [Matrix.mulVec_add]
  refine ⟨L₁.add_mem pa pb, L₂.add_mem ?_ (hb.2 ⟨pb, h2 b hb3⟩), ?_⟩
  · have := L₂.sub_mem ha2 (hb.2 ⟨L₁.sub_mem ha1 pa, h3 a ha1⟩)
    rwa [sub_sub_cancel] at this
  · rw [add_sub_add_comm]
    exact L₃.add_mem (h3 a ha1) (L₃.sub_mem hb3 (h2 b hb3))

theorem dist_La : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), (∀ (L : Lat D N) (L₁ L₂ L₃ : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L L₁) (La D (tor0 D cc δ) L L₂) (La D (tor0 D cc δ) L L₃)) ∧ (∀ (L₁ L₂ L₃ : Lat D N) (L' : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L₁ L') (La D (tor0 D cc δ) L₂ L') (La D (tor0 D cc δ) L₃ L')) ∧ ∀ (L₀ L : Lat D N) (L₀' L' : Lat D N'), SD D L₀' → SD D L' → Dist (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L₀ L') (La D (tor0 D cc δ) L L') := by
  intro D cc δ N N'
  refine ⟨?_, ?_, ?_⟩
  · intro L L₁ L₂ L₃ s1 s3 hb x hx y _ _
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N' L₁ L₃ s1 s3
    have k := bet_proj hb h1 h2 h3
    rw [← lft_add P x]
    refine add_mem (AddSubgroup.mem_sup_left ⟨lft_mem cc δ P (fun v hv => (k v hv).1) hx,
      lft_mem cc δ P (fun v hv => (k v hv).2.1) hx⟩) (AddSubgroup.mem_sup_right
        ⟨lft_mem cc δ _ (fun v hv => ?_) hx, lft_mem cc δ _ (fun v hv => ?_) hx⟩)
    · rw [one_sub_mulVec]; exact L₂.sub_mem hv (k v hv).2.1
    · rw [one_sub_mulVec]; exact (k v hv).2.2
  · intro L₁ L₂ L₃ L' s1 s3 hb x hx y _ _
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N L₁ L₃ s1 s3
    have k := bet_proj hb h1 h2 h3
    rw [← rgt_add P x, add_comm]
    refine add_mem (AddSubgroup.mem_sup_left ⟨rgt_mem cc δ _ (fun v hv => ?_) hx,
      rgt_mem cc δ _ (fun v hv => ?_) hx⟩) (AddSubgroup.mem_sup_right
        ⟨rgt_mem cc δ P (fun v hv => (k v hv).2.1) hx,
          rgt_mem cc δ P (fun v hv => hb.2 ⟨h1 v (Submodule.mem_sup_right hv), h2 v hv⟩) hx⟩)
    · rw [one_sub_mulVec]; exact hb.2 ⟨L₁.sub_mem hv (h1 v (Submodule.mem_sup_left hv)), h3 v hv⟩
    · rw [one_sub_mulVec]; exact L₂.sub_mem hv (k v hv).2.1
  · intro L₀ L L₀' L' s1 s3 x hx y hy hu
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N' L₀' L' s1 s3
    have q1 : ∀ v ∈ L₀', (1 - P).mulVec v ∈ L₀' := fun v hv => by
      rw [one_sub_mulVec]; exact L₀'.sub_mem hv (h1 v (Submodule.mem_sup_left hv))
    have q2 : ∀ v ∈ L₀', (1 - P).mulVec v ∈ L' := fun v hv => by
      rw [one_sub_mulVec]; exact h3 v hv
    have q3 : ∀ v ∈ L', (1 - P).mulVec v ∈ L' := fun v hv => by
      rw [one_sub_mulVec]; exact L'.sub_mem hv (h2 v hv)
    have e : x = lft P x + lft (1 - P) (x + y) - lft (1 - P) y := by
      rw [map_add (f := _), ← add_assoc, lft_add, add_sub_cancel_right]
    have e2 : lft (1 - P) y = lft (1 - P) (x + y) - lft (1 - P) x := by
      rw [map_add (f := _), add_sub_cancel_left]
    rw [e]
    refine sub_mem (AddSubgroup.mem_sup_left (add_mem
      ⟨lft_mem cc δ P (fun v hv => h1 v (Submodule.mem_sup_right hv)) hx, lft_mem cc δ P h2 hx⟩
      ⟨lft_mem cc δ _ q1 hu, lft_mem cc δ _ q2 hu⟩)) (AddSubgroup.mem_sup_right ⟨?_, lft_mem cc δ _ q3 hy⟩)
    rw [e2]
    exact AddSubgroup.sub_mem _ (lft_mem cc δ _ q2 hu) (lft_mem cc δ _ q3 hx)

end GlobalTheory.DistLa
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TripleConstant

theorem Wd_mul_sum (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') (c : ℂ) {ι : Type} (s : Finset ι)
    (G : ι → VC D N N' → ℂ) (v : VC D N N') :
    Wd D T y (fun z => c * ∑ i ∈ s, G i z) v = c * ∑ i ∈ s, Wd D T y (G i) v := by
  simp only [Wd, U, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem out_mem_iff {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (q : B ⧸ A.addSubgroupOf B) :
    ((Quotient.out q : B) : V) ∈ A ↔ q = 0 := by
  rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']

theorem mu_form : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∃ r : ℝ, 0 < r ∧ μ * (r : ℂ) = ∑ᶠ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂), (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) := by
  intro D T N N' A₁ A₂ A₃ e μ h
  obtain ⟨h1, h2, h3, n12, n23, n13, he, he0, -, hI⟩ := h
  haveI f12 : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.fintypeOfIndexNeZero n12
  haveI f23 : Fintype (A₃ ⧸ A₂.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n23
  haveI f13 : Fintype (A₃ ⧸ A₁.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n13
  rw [h3.Iop_eq A₂, h2.Iop_eq A₁, h3.Iop_eq A₁] at hI
  simp only [finsum_eq_sum_of_fintype] at hI ⊢
  have p12 : 0 < Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n12))
  have p23 : 0 < Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n23))
  have p13 : 0 < Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n13))
  generalize Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) = s12 at *
  generalize Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) = s23 at *
  generalize Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) = s13 at *
  have key := GlobalTheory.T.thetaTranslate_combination_coef_eq_zero D T N N' A₁ h1 e he he0
    (((A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂)) ⊕ (A₃ ⧸ A₁.addSubgroupOf A₃))
    (Sum.elim (fun p => (s23 : ℂ)⁻¹ * (s12 : ℂ)⁻¹ *
        bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun _ => -(μ * (s13 : ℂ)⁻¹)))
    (Sum.elim (fun p => ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun q => ((Quotient.out q : A₃) : VC D N N'))) (by
      intro v
      have hv := congrFun hI v
      simp only [Wd_mul_sum, Wd_Wd, Pi.smul_apply, smul_eq_mul] at hv
      simp only [Finset.mul_sum] at hv
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, neg_mul,
        Finset.sum_neg_distrib, mul_assoc]
      rw [hv]; ring)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, out_mem_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at key
  refine ⟨s23 * s12 / s13, by positivity, ?_⟩
  have q12 : (s12 : ℂ) ≠ 0 := by exact_mod_cast p12.ne'
  have q23 : (s23 : ℂ) ≠ 0 := by exact_mod_cast p23.ne'
  have q13 : (s13 : ℂ) ≠ 0 := by exact_mod_cast p13.ne'
  have k2 := congrArg (fun t => (s23 : ℂ) * s12 * t) (add_neg_eq_zero.1 key)
  simp only [Finset.mul_sum] at k2
  have : μ * ((s23 * s12 / s13 : ℝ) : ℂ) = (s23 : ℂ) * s12 * (μ * (s13 : ℂ)⁻¹) := by
    push_cast; ring
  rw [this, ← k2]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁
  · simp only [hp, if_true]
    field_simp
  · simp only [hp, if_false, mul_zero]

end GlobalTheory.TripleConstant
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.KumIdeal

theorem exists_mul_modEq_ppow {p : ℕ} (hp : p.Prime) {n a : ℕ} (hn : 1 ≤ n) (ha : ¬ p ^ n ∣ a) :
    ∃ k, k * a ≡ p ^ (n - 1) [MOD p ^ n] := by
  have hd : Nat.gcd a (p ^ n) ∣ p ^ n := Nat.gcd_dvd_right _ _
  obtain ⟨v, hv, hv'⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hvn : v ≠ n := by
    intro h; apply ha; rw [← h, ← hv']; exact Nat.gcd_dvd_left _ _
  have hlt : Nat.gcd a (p ^ n) < p ^ n := by
    rw [hv']; exact Nat.pow_lt_pow_right hp.one_lt (lt_of_le_of_ne hv hvn)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
  refine ⟨m * p ^ (n - 1 - v), ?_⟩
  have e : p ^ (n - 1) = p ^ v * p ^ (n - 1 - v) := by rw [← pow_add]; congr 1; omega
  rw [e, ← hv', ← hm]
  calc m * p ^ (n - 1 - v) * a = (a * m) * p ^ (n - 1 - v) := by ring
    _ ≡ (a * m % p ^ n) * p ^ (n - 1 - v) [MOD p ^ n] := (Nat.mod_modEq _ _).symm.mul_right _

theorem zeta_sub_one_mem_span : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ j : ℕ, 1 ≤ j → ∀ g ∈ Hinf T, g r ≠ r →
  T.ζ j - 1 ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x} := by
  intro p _ hp2 Ω _ _ hΩ T n r hr hK j hj g hg hgr
  classical
  have hp : p.Prime := Fact.out
  set C := FixI (Hfix T r) with hC
  set I := Submodule.span C {y : Ω | ∃ x ∈ C, y = g x - x} with hI
  have hr0 : r ≠ 0 := by rintro rfl; exact hgr (map_zero g)
  obtain ⟨y, E, hy, hE, huniq, hsum⟩ :=
    GlobalTheory.T.exists_integral_sum_conj_eq_zeta_sub_one p hp2 Ω hΩ T {r} (by simpa using hr) j hj
  have hE' : ∀ e ∈ E, e ∈ Hinf T := hE
  have huniq' : ∀ h ∈ Hinf T, ∃! e, e ∈ E ∧ h y = e y ∧ h r = e r := by
    intro h hh; simpa using huniq h hh
  have hex : ∀ k : Gal p Ω, ∃ e, k ∈ Hinf T → e ∈ E ∧ k y = e y ∧ k r = e r := by
    intro k
    by_cases hk : k ∈ Hinf T
    · obtain ⟨e, he, -⟩ := huniq' k hk; exact ⟨e, fun _ => he⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose rep hrep using hex
  have runiq : ∀ k ∈ Hinf T, ∀ e ∈ E, k y = e y → k r = e r → rep k = e := fun k hk e he h1 h2 =>
    (huniq' k hk).unique (hrep k hk) ⟨he, h1, h2⟩
  have hinv : ∀ h : Gal p Ω, ∀ x, h⁻¹ (h x) = x := fun h x => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hinv' : ∀ h : Gal p Ω, ∀ x, h (h⁻¹ x) = x := fun h x => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  let Y : Ω → Ω := fun ρ => ∑ e ∈ E with e r = ρ, e y
  have hYgal : ∀ h ∈ Hinf T, ∀ ρ, h (Y ρ) = Y (h ρ) := by
    intro h hh ρ

    simp only [Y, map_sum]
    have hmem : ∀ k ∈ Hinf T, ∀ e ∈ E, k * e ∈ Hinf T := fun k hk e he => mul_mem hk (hE' e he)
    refine Finset.sum_nbij' (fun e => rep (h * e)) (fun e => rep (h⁻¹ * e)) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨h1, -, h3⟩ := hrep _ (hmem h hh e he.1)
      exact ⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2]⟩
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨h1, -, h3⟩ := hrep _ (hmem _ (inv_mem hh) e he.1)
      exact ⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2, hinv]⟩
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨h1, h2, h3⟩ := hrep _ (hmem h hh e he.1)
      refine runiq _ (hmem _ (inv_mem hh) _ h1) e he.1 ?_ ?_
      · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv]
      · rw [AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv]
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨h1, h2, h3⟩ := hrep _ (hmem _ (inv_mem hh) e he.1)
      refine runiq _ (hmem _ hh _ h1) e he.1 ?_ ?_
      · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv']
      · rw [AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv']
    · intro e he
      simp only [Finset.mem_filter] at he
      exact (hrep _ (hmem h hh e he.1)).2.1

  have hzn := T.prim n
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  have hζr : ∀ i : ℕ, T.ζ n ^ i = T.ζ n ^ (i % p ^ n) := fun i => by
    conv_lhs => rw [← Nat.mod_add_div i (p ^ n), pow_add, pow_mul, hzn.pow_eq_one, one_pow, mul_one]
  let Z : ℕ → Ω := fun i => Y (T.ζ n ^ i * r)
  have hZC : ∀ i, Z i ∈ C := by
    intro i
    refine ⟨int_sum _ _ fun e _ => int_gal e hy, fun h hh => ?_⟩
    rw [mem_Hfix] at hh
    show h (Y _) = Y _
    rw [hYgal h hh.1, map_mul, map_pow, (mem_Hinf.1 hh.1 n).1, hh.2]
  have hZmod : ∀ i i', i ≡ i' [MOD p ^ n] → Z i = Z i' := by
    intro i i' h
    show Y _ = Y _
    rw [(GlobalTheory.K5.Basic.zeta_pow_eq_iff T n i i').2 h]
  obtain ⟨a, ha⟩ := hK g hg
  have hZg : ∀ i, g (Z i) = Z (i + a) := by
    intro i
    show g (Y _) = Y _
    rw [hYgal g hg, map_mul, map_pow, (mem_Hinf.1 hg n).1, ha, pow_add, mul_assoc]
  have hZa : ∀ i, Z (i + a) - Z i ∈ I := fun i => by
    rw [← hZg]; exact Submodule.subset_span ⟨Z i, hZC i, rfl⟩
  have iter : ∀ b, (∀ i, Z (i + b) - Z i ∈ I) → ∀ t i, Z (i + t * b) - Z i ∈ I := by
    intro b hb t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      have e : i + (t + 1) * b = (i + t * b) + b := by ring
      rw [e]
      have := I.add_mem (hb (i + t * b)) (ih i)
      rwa [sub_add_sub_cancel] at this
  have hn : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    apply hgr
    rw [ha, hζr, hn0, pow_zero, Nat.mod_one, pow_zero, one_mul]
  have hna : ¬ p ^ n ∣ a := by
    intro hd
    apply hgr
    rw [ha, hζr, Nat.eq_zero_of_dvd_of_lt ?_ (Nat.mod_lt a hpos), pow_zero, one_mul]
    exact (Nat.dvd_mod_iff dvd_rfl).2 hd
  obtain ⟨k, hk⟩ := exists_mul_modEq_ppow hp hn hna
  have hZd : ∀ i, Z (i + p ^ (n - 1)) - Z i ∈ I := by
    intro i
    rw [hZmod (i + p ^ (n - 1)) (i + k * a) (Nat.ModEq.add_left i hk.symm)]
    exact iter a hZa k i
  set d := p ^ (n - 1) with hd
  set W := ∑ i ∈ Finset.range d, Z i with hW
  have hWC : W ∈ C := Subalgebra.sum_mem _ fun i _ => hZC i
  have hsumW : ∀ t : ℕ, ∑ i ∈ Finset.range (t * d), Z i - (t : Ω) * W ∈ I := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have e : (t + 1) * d = t * d + d := by ring
      rw [e, Finset.sum_range_add]
      have h2 : ∑ x ∈ Finset.range d, Z (t * d + x) - W ∈ I := by
        rw [hW, ← Finset.sum_sub_distrib]
        refine Submodule.sum_mem _ fun x _ => ?_
        rw [add_comm]; exact iter d hZd t x
      have := I.add_mem ih h2
      convert this using 1
      push_cast; ring
  have hNd : p * d = p ^ n := by
    rw [hd, ← pow_succ']; congr 1; omega
  have hsumZ : ∑ i ∈ Finset.range (p ^ n), Z i = T.ζ j - 1 := by
    rw [← hsum]
    have hinj : Set.InjOn (fun i => T.ζ n ^ i * r) (Finset.range (p ^ n) : Set ℕ) := by
      intro i hi i' hi' h
      simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
      exact hzn.pow_inj hi hi' (mul_right_cancel₀ hr0 h)
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r))
      (g := fun e : Gal p Ω => e r)]
    · rw [Finset.sum_image hinj]
    · intro e he
      obtain ⟨i, hi⟩ := hK e (hE' e he)
      rw [Finset.mem_image]
      exact ⟨i % p ^ n, Finset.mem_range.2 (Nat.mod_lt _ hpos), by rw [← hζr, hi]⟩
  have hτI : T.ζ j - 1 - (p : Ω) * W ∈ I := by
    have := hsumW p
    rwa [hNd, hsumZ] at this
  have hτ0 : T.ζ j - 1 ≠ 0 :=
    sub_ne_zero.2 ((T.prim j).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))
  obtain ⟨hu0, huint⟩ := GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit p hp2 Ω hΩ T j hj W hWC.1
  have huC : (1 - (p : Ω) / (T.ζ j - 1) * W)⁻¹ ∈ C := by
    refine ⟨huint, fun h hh => ?_⟩
    rw [mem_Hfix] at hh
    rw [map_inv₀, map_sub, map_one, map_mul, map_div₀, map_sub, map_one, map_natCast,
      (mem_Hinf.1 hh.1 j).1, hWC.2 h (by rw [mem_Hfix]; exact hh)]
  have := I.smul_mem (⟨_, huC⟩ : C) hτI
  rw [Subalgebra.smul_def, smul_eq_mul] at this
  have key : T.ζ j - 1 - (p : Ω) * W = (1 - (p : Ω) / (T.ζ j - 1) * W) * (T.ζ j - 1) := by
    have e2 : (p : Ω) / (T.ζ j - 1) * W * (T.ζ j - 1) = (p : Ω) * W := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hτ0]
    rw [sub_mul, one_mul, e2]
  rw [key, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul] at this
  exact this

end GlobalTheory.KumIdeal
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PsType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PsType

theorem ineIncl_onto_units : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ u : (w.adicCompletion E)ˣ, valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 → ∃ s : ↥(Ine (F := E) A), a (ineIncl h s) = u) ∧ ∀ s : ↥(Ine (F := E) A), valuation (w.adicCompletion E) (a (ineIncl h s) : w.adicCompletion E) = 1 := by
  intro E Ω _ _ _ _ _ A w h a ha
  refine ⟨fun u hu => ?_, fun s => ?_⟩
  · obtain ⟨τ, rfl⟩ := ha.surj u
    have hdeg : deg τ = 0 := by
      have := ha.ord_eq τ
      rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 hu] at this
      omega
    exact ⟨⟨τ, deg_eq_zero_iff.1 hdeg⟩, congrArg a (Subtype.ext (by rw [coe_ineIncl]))⟩
  · exact GlobalTheory.SmGL.ord_eq_zero_iff.1 (by rw [ha.ord_eq, deg_ineIncl, neg_zero])

end GlobalTheory.PsType
end
