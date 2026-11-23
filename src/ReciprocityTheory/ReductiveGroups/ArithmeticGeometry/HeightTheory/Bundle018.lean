module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SacSuccAbove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Norm.Transitivity
public import ReciprocityTheory.SemistableReduction.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle016

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial MeasureTheory

theorem countable_numberField (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem ST_scale (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ) (y : Fin (d.N + 1 + d.D) → ℂ)
    (hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0) :
    d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t := by
  ext P
  simp only [ST, Set.mem_setOf_eq, NPB.gpt, Fin.cases_succ]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_eq_zero]
  simp [hy i]

theorem gpt_one (t : Fin d.D → Fin (d.N + 1) → ℂ) (t0 : Fin (d.N + 1) → ℂ) :
    NPB.gpt (fun q => t q.1 q.2) (Fin.addCases t0 (fun _ => (1 : ℂ))) =
      fun v : TVar d.D d.N => Fin.cases (motive := fun _ => ℂ) (t0 v.2) (fun i => t i v.2) v.1 := by
  funext v
  rcases v with ⟨a, j⟩
  refine Fin.cases ?_ (fun i => ?_) a <;> simp [NPB.gpt]

theorem fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    (d.ST c sg t).Finite ∧ (d.ST c sg t).ncard = d.delc c ∧
      (∀ g : Ω c, tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))
        = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g) ∧
      tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) =
        ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
          ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
  letI iA : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iB : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra
  obtain ⟨hfd, hrank⟩ := d.omS_finite hd h c
  haveI := hfd
  haveI : CharZero (KTf K d.D d.N) := inferInstance
  haveI : Algebra.IsIntegral (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsSeparable.of_integral _ _
  have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := by
    intro i h0
    apply hpt (MvPolynomial.X (i.succ, 0)) (MvPolynomial.X_ne_zero _)
    simp [NPB.gpt, h0]
  have hST : d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t :=
    d.ST_scale c sg t y hy
  obtain ⟨hinj, hrange⟩ := d.fibre_core (hd := hd) (h := h) (c := c) (sg := sg)
    (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt)
  rw [hST] at hrange
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact Set.finite_range _
  · rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, AlgHom.card, hrank]
  · intro g
    have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ
      (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    exact h1
  · have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ (d.rationalBaseRow c)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    refine h1.trans (Finset.prod_congr rfl fun σ _ => ?_)
    have hσ : (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg _ hpt :=
      RingHom.ext fun x => σ.commutes x

    simp only [rationalBaseRow, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have he := d.emb_sH (h := h) (c := c) (sg := sg)
      (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt) (σ : OmS (Ω c) d.D d.N →+* ℂ) hσ
      (MvPolynomial.X (0, j))
    simp only [AlgHom.coe_toRingHom] at he
    rw [he]
    simp [NPB.gpt]

theorem norm_at_sg_B (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have := countable_numberField K
  filter_upwards [NPB.ae_gen (K := K) (D := d.D) (N := d.N) sg] with z hz
  have hG : ∀ (a : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K),
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a p → p ≠ 0 →
        eval₂ sg (fun q => d.tOf z q.1 q.2) p ≠ 0 := hz
  obtain ⟨y1, -, hpt1⟩ := NPB.exists_gen sg (fun q => d.tOf z q.1 q.2) hG 1 one_ne_zero
  obtain ⟨hfin, hcard, -, -⟩ := d.fib hd h c sg (d.tOf z) y1 hpt1
  refine ⟨hfin, hcard, ?_, ?_⟩
  · intro g a b t0 _ _ hab hbt
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a -
        C (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) *
          NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, hn, -⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn g, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    rw [div_eq_iff hbt]
    exact h2
  · intro a b t0 _ hab hbt
    let cX : MvPolynomial (Fin (d.N + 1 + d.D)) ℂ := ∏ P ∈ hfin.toFinset,
      ∑ j, X (Fin.castAdd d.D j) * C (P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)))
    have hcX : ∀ y, eval y cX = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
      intro y
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]

      simp only [cX, map_prod, map_sum, map_mul, eval_X, eval_C]
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a - cX * NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, -, hn⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    simp only [Fin.addCases_left] at h2
    rw [div_eq_iff hbt]
    exact h2

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

theorem evT_eq_blockPoint_of_mh (sg : K →+* ℂ) (q : KTp K d.D d.N) (hq : q ≠ 0) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    ∃ g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ, g ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun i : Fin d.D => m i.succ) g ∧
      ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
  classical
  set φ : Fin d.D × Fin (d.N + 1) → TVar d.D d.N := fun p => (p.1.succ, p.2) with hφ
  have hφi : Function.Injective φ := fun p p' h => by
    simp only [hφ, Prod.mk.injEq] at h
    exact Prod.ext (Fin.succ_injective _ h.1) h.2
  have hvars : (q.vars : Set (TVar d.D d.N)) ⊆ Set.range φ := by
    intro v hv
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hv
    obtain ⟨s, hs, hsv⟩ := hv
    have h0 : v.1 ≠ 0 := by
      intro h0
      have h1 := hqm s hs 0
      rw [hm] at h1
      have hz := (Finset.sum_eq_zero_iff.1 h1) v.2 (Finset.mem_univ _)
      apply (Finsupp.mem_support_iff.1 hsv)
      have e : v = (0, v.2) := Prod.ext h0 rfl
      rw [e]; exact hz
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.2 h0
    exact ⟨(i, v.2), Prod.ext hi rfl⟩
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q φ hφi hvars
  set g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ := MvPolynomial.map sg q' with hgdef
  have heval : ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
    intro z
    rw [← hq', evT, MvPolynomial.eval₂_rename, hgdef, MvPolynomial.eval_map]
    congr 1
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    exact hq (by rw [← hq', map_zero])
  have hg0 : g ≠ 0 := by
    intro h0
    apply hq'0
    apply MvPolynomial.map_injective sg sg.injective
    rw [← hgdef, h0, map_zero]
  have hgm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun i : Fin d.D => m i.succ) g := by
    intro s hs b
    have hs' : s ∈ q'.support := MvPolynomial.support_map_subset _ _ hs
    have hsq : Finsupp.mapDomain φ s ∈ q.support := by
      rw [← hq', MvPolynomial.support_rename_of_injective hφi]
      exact Finset.mem_image_of_mem _ hs'
    show _ = m b.succ
    rw [← hqm _ hsq b.succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finsupp.mapDomain_apply_of_injective hφi s (b, j)).symm
  exact ⟨g, hg0, hgm, heval⟩

theorem logInt_evT_of_mh (sg : K →+* ℂ) (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) q‖)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  by_cases hq : q = 0
  · subst hq
    simp [evT]
  · obtain ⟨g, hg, hgm, heq⟩ := d.evT_eq_blockPoint_of_mh sg q hq m hm hqm
    simp_rw [heq]
    exact ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable d.D (d.N + 1) _ g hg hgm

theorem integrable_log_norm_sub_log_norm (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) a‖ -
      Real.log ‖d.evT sg 0 (d.tOf z) b‖) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  obtain ⟨-, -, m, hm0, hma, hmb⟩ := hab
  exact (d.logInt_evT_of_mh sg a m hm0 hma).sub (d.logInt_evT_of_mh sg b m hm0 hmb)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem hx4v2_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {g : V}
    (hg : g ≠ 0) (s : Ω) : ratio (Ω := Ω) (s • g) g = s := by
  unfold ratio
  have hex : ∃ a : Ω, s • g = a • g := ⟨s, rfl⟩
  rw [dite_eq_left hex]
  exact (smul_left_injective Ω hg hex.choose_spec).symm

theorem hx4v2_eq_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (W : Submodule Ω V) (hW : Module.finrank Ω W = 1) {f g : V} (hf : f ∈ W) (hgW : g ∈ W)
    (hg : g ≠ 0) : f = ratio (Ω := Ω) f g • g := by
  have hg' : (⟨g, hgW⟩ : W) ≠ 0 := fun e => hg (congrArg Subtype.val e)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hgW⟩ : W) hg').mp hW ⟨f, hf⟩
  have hex : ∃ a : Ω, f = a • g := ⟨a, (congrArg Subtype.val ha).symm⟩
  unfold ratio
  rw [dite_eq_left hex]
  exact hex.choose_spec

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hx4v2_ratio_wx (hd : d.AxH 𝒜) (c : ι) (x : Fin (d.N + 1) → K) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  have := hd.tower c
  have hg := hd.w_base c
  have hrep : ∀ j, d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    fun j => hx4v2_eq_ratio_smul _ (hd.finrank_one c d.wL) (hd.w_mem j c) (hd.w_mem (d.jc c) c) hg
  have hsum : d.wx x c = (∑ j, algebraMap K (Ω c) (x j) *
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [hrep j]
    rw [mul_smul, algebraMap_smul]
  rw [hsum, hx4v2_ratio_smul hg]

theorem norm_generic_ratio_spec (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x Q = Q) ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 →
        (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x P) =
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
              Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
                (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)))) := by
  let _ : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨n, b, Q0, M, hQ0, hQ0s, hMs, hM⟩ :=
    ReciprocityTheory.ChartRestriction.G.T0.Data.basis_block0 d hd h c
  let r : Fin (d.N + 1) → OmS (Ω c) d.D d.N := fun j =>
    algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))
  let ι0 : KTp K d.D d.N →+* KTf K d.D d.N := algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
  have hQ0' : ι0 Q0 ≠ 0 := fun e =>
    hQ0 (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (by rw [e, map_zero]))
  have key : ∀ a : Fin (d.N + 1) → KTp K d.D d.N,
      Algebra.norm (KTf K d.D d.N) (∑ j, ι0 (a j) • r j) = ι0 (∑ j, a j • M j).det / ι0 Q0 ^ n := by
    intro a

    rw [Algebra.norm_eq_matrix_det b, map_sum]
    simp_rw [map_smul]
    have hmat : (∑ j, ι0 (a j) • Algebra.leftMulMatrix b (r j)) =
        (ι0 Q0)⁻¹ • (∑ j, a j • M j).map ι0 := by
      ext i i'

      rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.sum_apply, map_sum,
      Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM j, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, map_mul]
      ring
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
    have hdet : ((∑ j, a j • M j).map ι0).det = ι0 (∑ j, a j • M j).det :=
      (RingHom.map_det ι0 _).symm
    rw [hdet, inv_pow, div_eq_mul_inv, mul_comm]
  have hw0 : d.rationalBaseRow c = ∑ j, ι0 (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • r j := by
    simp only [Data.rationalBaseRow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, r]
  refine ⟨(∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det, Q0 ^ n, pow_ne_zero _ hQ0,
    fun x => by rw [map_pow, hQ0s], ?_, ?_⟩
  · show ι0 _ = ι0 (Q0 ^ n) * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)
    rw [hw0, key, map_pow]
    field_simp
  · intro x _
    have hs : d.sub0 x (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det =
        (∑ j, (MvPolynomial.C (x j) : KTp K d.D d.N) • M j).det := by
      have hmd := RingHom.map_det (d.sub0 x : KTp K d.D d.N →+* KTp K d.D d.N)
        (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j)
      rw [RingHom.coe_coe] at hmd
      rw [hmd]
      congr 1
      ext i i'

      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, RingHom.coe_coe, hMs]
      simp
    have hr : algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)) =
        ∑ j, ι0 (MvPolynomial.C (x j) : KTp K d.D d.N) • r j := by

      rw [d.hx4v2_ratio_wx hd c x, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      congr 1
      simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N) (x j)).symm
    show ι0 _ = ι0 (Q0 ^ n) * _
    rw [hs, hr, key, map_pow]
    field_simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
