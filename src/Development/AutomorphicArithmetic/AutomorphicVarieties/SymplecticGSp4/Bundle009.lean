module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.aElt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ g, ∃ a ∈ M.gr 0, M.x0 a = 0 ∧ ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ (M.toSS a) = D.aVal g (M.rep ξ) := by
  intro Ω _ _ _ l _ c D _ M g
  choose f hf hπ using fun i : Fin 4 => M.hom g i i
  have hf0 : ∀ i, f i ∈ M.aPart 0 := by
    intro i
    have h := hf i
    rw [(wt_eq_zero i i).mpr rfl] at h
    exact h
  let fA : Fin 4 → M.A := fun i => ⟨f i, M.aPart_le (hf0 i)⟩
  have hx0 : ∀ i, M.x0 (fA i) = D.r0 g i i := fun i => M.at0 g i i (f i) (hπ i)
  have hss : ∀ i, M.toSS (fA i) = M.ent g i i := fun i => Subtype.ext (hπ i)
  refine ⟨∑ i, fA i - algebraMap c.O M.A (Matrix.trace (D.r0 g)), ?_, ?_, ?_⟩
  · apply Submodule.sub_mem
    · exact Submodule.sum_mem _ fun i _ => hf0 i
    · rw [Algebra.algebraMap_eq_smul_one]
      apply Submodule.smul_mem
      show (1 : M.R) ∈ M.aPart 0
      exact SetLike.GradedOne.one_mem
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, AlgHom.commutes]
    simp only [hx0, Algebra.algebraMap_self, RingHom.id_apply, Matrix.trace, Matrix.diag]
    exact sub_self _
  · intro ξ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, AlgHom.commutes, AlgHom.commutes]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hss, Raw.aVal, Matrix.trace, Matrix.diag, map_sum]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem wcomp_self_eq_of_mem_wtPart {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) : wcomp O wt j f = f := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp]
  by_cases h1 : Finsupp.weight wt n = j
  · rw [if_pos h1]
  · rw [if_neg h1]
    exact (hf' n h1).symm

private theorem wcomp_eq_zero_of_mem_wtPart_of_ne {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) {j' : X} (hj : j' ≠ j) : wcomp O wt j' f = 0 := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp, map_zero]
  by_cases h1 : Finsupp.weight wt n = j'
  · rw [if_pos h1]
    exact hf' n (by rw [h1]; exact hj)
  · rw [if_neg h1]

private theorem aGraded_internal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (M : Model D) : DirectSum.IsInternal M.gr := by
  set_option synthInstance.maxHeartbeats 200000 in
    have key : ∀ (n : ℤ) (x : M.R), x ∈ M.aPart n → x ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) → x = 0 := by
      intro n x hx hx'
      have hle : (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) ≤
          Submodule.map M.W.π.toLinearMap
            (LinearMap.ker (M.W.π.toLinearMap ∘ₗ wcomp c.O M.W.wt ((0 : ℤ), n))) := by
        refine iSup₂_le fun m hm => ?_
        rintro y ⟨h, hh, rfl⟩
        refine ⟨h, ?_, rfl⟩
        change M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) h) = 0
        rw [wcomp_eq_zero_of_mem_wtPart_of_ne hh, map_zero]
        intro h'
        exact hm (Prod.ext_iff.mp h').2.symm
      obtain ⟨g, hg, hgx⟩ := hle hx'
      obtain ⟨f, hf, rfl⟩ := hx
      have hker : f - g ∈ RingHom.ker M.W.π := by
        rw [RingHom.mem_ker, map_sub]
        exact sub_eq_zero.mpr hgx.symm
      have h2 := M.W.homog _ hker ((0 : ℤ), n)
      rw [RingHom.mem_ker, map_sub, map_sub] at h2
      have hg' : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) = 0 := hg
      have h3 : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) = M.W.π f := by
        rw [wcomp_self_eq_of_mem_wtPart hf]
      change M.W.π f = 0
      calc M.W.π f = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) := h3.symm
        _ = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) := sub_eq_zero.mp h2
        _ = 0 := hg'
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro n
      rw [Submodule.disjoint_def]
      intro x hx hx'
      have h1 : (x : M.R) ∈ M.aPart n := hx
      have h2 : (x : M.R) ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) := by
        have := Submodule.mem_map_of_mem (f := M.A.val.toLinearMap) hx'
        simp only [Submodule.map_iSup] at this
        exact (iSup₂_mono fun m _ => Submodule.map_comap_le _ _) this
      exact Subtype.ext (key n _ h1 h2)
    · refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨y, hy⟩ := x
      have main : ∀ (z : M.R) (hz : z ∈ ⨆ n, M.aPart n), (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n := by
        intro z hz
        refine Submodule.iSup_induction' M.aPart
          (motive := fun z hz => (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n) ?_ ?_ ?_ hz
        · intro n w hw
          exact Submodule.mem_iSup_of_mem n hw
        · exact zero_mem _
        · intro a b ha hb iha ihb
          exact add_mem iha ihb
      exact main y hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aGraded :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, Nonempty (GradedAlgebra M.gr) := by
  intro Ω _ _ _ l _ c D _ M
  exact ⟨{ (inferInstance : SetLike.GradedMonoid M.gr), (aGraded_internal M).chooseDecomposition with }⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem aW_comb {σ : Type} [Fintype σ] (lam : σ → ℤ) (hl : ∀ s, lam s = -1 ∨ lam s = 0 ∨ lam s = 1)
    (P : (σ →₀ ℕ) → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (h1 : ∀ s, lam s = 0 → P (Finsupp.single s 1))
    (h2 : ∀ s t, lam s = 1 → lam t = -1 → P (Finsupp.single s 1 + Finsupp.single t 1)) :
    ∀ m, Finsupp.weight lam m = 0 → P m := by
  classical
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro hm
  have step : ∀ g : σ →₀ ℕ, g ≠ 0 → g ≤ m → Finsupp.weight lam g = 0 → P g → P m := fun g hg hle hw hP => by
    have e : m - g + g = m := tsub_add_cancel_of_le hle
    have hlt : m - g < m := by
      conv_rhs => rw [← e]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hg)
    have hw' : Finsupp.weight lam (m - g) = 0 := by
      have := congrArg (Finsupp.weight lam) e
      rwa [map_add, hw, add_zero, hm] at this
    rw [← e]
    exact hadd _ _ (ih _ hlt hw') hP
  by_cases hz : ∃ s, m s ≠ 0 ∧ lam s = 0
  · obtain ⟨s, hs, hs0⟩ := hz
    refine step (Finsupp.single s 1) (by simp) ?_ (by simp [Finsupp.weight_single, hs0]) (h1 s hs0)
    rw [Finsupp.single_le_iff]
    omega
  by_cases hp : (∃ s, m s ≠ 0 ∧ lam s = 1) ∧ ∃ t, m t ≠ 0 ∧ lam t = -1
  · obtain ⟨⟨s, hs, hs1⟩, t, ht, ht1⟩ := hp
    have hst : s ≠ t := by
      rintro rfl
      omega
    refine step _ (by simp) ?_ (by simp [Finsupp.weight_single, hs1, ht1]) (h2 s t hs1 ht1)
    intro u
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with a b b
    · exact absurd (a.trans b.symm) hst
    · subst a; omega
    · subst b; omega
    · omega
  have hsum : ∑ s, (m s : ℤ) * lam s = 0 := by
    rw [← hm, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : m = 0 := by
    ext u
    push Not at hz
    rcases not_and_or.1 hp with hp | hp
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, (m s : ℤ) * lam s ≤ 0 := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonpos hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, 0 ≤ (m s : ℤ) * lam s := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonneg (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
  rw [this]
  exact h0

private theorem aW_wts : ∀ w ∈ wts, (w.1 = -1 ∨ w.1 = 0 ∨ w.1 = 1) ∧ (-1 ≤ w.2 ∧ w.2 ≤ 1) := by decide

private theorem aW_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (B : Subalgebra O R) (h0 : ∀ x ∈ W.part 0, x ∈ B)
    (h1 : ∀ s, (W.wt s).1 = 0 → W.z s ∈ B)
    (h2 : ∀ s t, (W.wt s).1 = 1 → (W.wt t).1 = -1 → W.z s * W.z t ∈ B) (n : ℤ) :
    ∀ x ∈ W.part (0, n), x ∈ B := by
  have hmon : ∀ m, Finsupp.weight (fun s => (W.wt s).1) m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ B := by
    refine aW_comb _ (fun s => (aW_wts _ (hw s)).1) _ (by simp) (fun a b ha hb => ?_) h1 (fun s t hs ht => ?_)
    · have := mul_mem ha hb
      rwa [← map_mul, MvPowerSeries.monomial_mul_monomial, one_mul] at this
    · have := h2 s t hs ht
      rwa [WPres.z, WPres.z, ← map_mul, MvPowerSeries.X_def, MvPowerSeries.X_def,
        MvPowerSeries.monomial_mul_monomial, one_mul] at this
  have hfst : ∀ m : W.σ →₀ ℕ, Finsupp.weight (fun s => (W.wt s).1) m = (Finsupp.weight W.wt m).1 := fun m => by
    induction m using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, Prod.fst_add]
    | single s k => simp [Finsupp.weight_single]
  obtain ⟨μ, hμ, hdec⟩ := part_span O R (ℤ × ℤ) W {m | Finsupp.weight W.wt m = (0, n)} (0, n) (fun _ h => h)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨b, hb, rfl⟩ := hdec f hf
  show W.π _ ∈ _

  rw [map_sum]
  refine sum_mem fun m hm => ?_
  rw [map_mul]
  refine mul_mem (h0 _ ⟨b m, hb m, rfl⟩) (hmon m ?_)
  have : Finsupp.weight W.wt m = (0, n) := hμ hm
  rw [hfst, this]

private theorem weight_algebra_generated_degree_two {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (a : ℤ → Submodule O R) [SetLike.GradedMonoid a] (ha : ∀ n, a n = W.part (0, n)) :
    ∃ s : Finset (gradedSub a), (∀ x ∈ s, x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧
      Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ s) = ⊤ := by
  classical
  let U : Set R := Set.range W.z ∪ Set.range fun p : W.σ × W.σ => W.z p.1 * W.z p.2
  have hU : U.Finite := (Set.finite_range _).union (Set.finite_range _)
  let T : Set (gradedSub a) := {x | (x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧ x.1 ∈ U}
  have hT : T.Finite := (hU.preimage Subtype.val_injective.injOn).subset fun x hx => hx.2
  refine ⟨hT.toFinset, fun x hx => (hT.mem_toFinset.1 hx).1, ?_⟩
  rw [hT.coe_toFinset]
  set S := Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ T) with hS
  have key : ∀ n : ℤ, -2 ≤ n → n ≤ 2 → ∀ y ∈ W.part (0, n), y ∈ U → y ∈ S.map (gradedSub a).val := by
    intro n hn hn' y hy hyU
    rw [← ha] at hy
    refine ⟨⟨y, le_iSup a n hy⟩, Algebra.subset_adjoin ?_, rfl⟩
    have h4 : n = 0 ∨ n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2 := by omega
    rcases h4 with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hy
    · exact Or.inr ⟨Or.inl hy, hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inl hy), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hy)), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr hy)), hyU⟩
  have main := aW_gen W hw (S.map (gradedSub a).val)
    (fun y hy => by
      have hy' : y ∈ a 0 := by rw [ha]; exact hy
      exact ⟨⟨y, le_iSup a 0 hy'⟩, Algebra.subset_adjoin (Or.inl hy'), rfl⟩)
    (fun s hs => by
      have hb := (aW_wts _ (hw s)).2
      refine key (W.wt s).2 (by omega) (by omega) _ ?_ (Or.inl ⟨s, rfl⟩)
      rw [← hs]
      exact W.z_mem s)
    (fun s t hs ht => by
      have hb := (aW_wts _ (hw s)).2
      have hb' := (aW_wts _ (hw t)).2
      refine key ((W.wt s).2 + (W.wt t).2) (by omega) (by omega) _ ?_ (Or.inr ⟨(s, t), rfl⟩)
      have h5 : W.z s * W.z t ∈ W.part (W.wt s + W.wt t) :=
        SetLike.GradedMul.mul_mem (W.z_mem s) (W.z_mem t)
      have h6 : W.wt s + W.wt t = (0, (W.wt s).2 + (W.wt t).2) :=
        Prod.ext (by rw [Prod.fst_add, hs, ht]; rfl) rfl
      rwa [h6] at h5)
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hxS : x ∈ S.map (gradedSub a).val :=
    Submodule.iSup_induction a (motive := fun x => x ∈ S.map (gradedSub a).val) hx (fun n y hy => main n y (ha n ▸ hy))
      (zero_mem _) (fun a b ha hb => add_mem ha hb)
  obtain ⟨y, hy, hxy⟩ := hxS
  obtain rfl : y = ⟨x, hx⟩ := Subtype.ext hxy
  exact hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aW :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], IsWRing M.gr M.x0 := by
  intro Ω _ _ _ l _ c D _ M _
  classical
  have hz : ∀ s, M.W.z s ∈ maximalIdeal M.R := fun s => by
    rw [← res_eq_zero_iff c.O, ← res_map (M.W.origin M.org), WPres.z, M.W.origin_π, MvPowerSeries.constantCoeff_X,
      map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    refine ⟨?_, ?_, ?_⟩
  · haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O (ℤ × ℤ) M.R M.W hz
    let p : M.W.gr 0 →ₐ[c.O] M.gr 0 :=
      { toFun := fun F => ⟨⟨F.1.1, M.aPart_le (n := 0) F.2⟩, F.2⟩
        map_one' := rfl
        map_mul' := fun F G => rfl
        map_zero' := rfl
        map_add' := fun F G => rfl
        commutes' := fun c => rfl }
    haveI : Nontrivial (M.gr 0) := ⟨⟨0, 1, fun h =>
      zero_ne_one (α := M.R) (congrArg (fun x : M.gr 0 => ((x : M.A) : M.R)) h)⟩⟩
    refine co_quot c.O (M.W.gr 0) (M.gr 0) p ?_
    rintro ⟨⟨x, hxA⟩, hx⟩
    exact ⟨⟨⟨x, M.W.part_le_A (j := 0) hx⟩, hx⟩, rfl⟩
  · exact weight_algebra_generated_degree_two M.W M.wt_mem M.aPart (fun _ => rfl)
  · rintro j hj f ⟨g, hg, hgf⟩
    have hgf' : M.W.π g = (f : M.R) := hgf
    show M.W.origin M.org (f : M.R) = 0
    rw [← hgf', M.W.origin_π, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hg 0 (by rw [map_zero]; exact fun h => hj (congrArg Prod.snd h).symm)
end
