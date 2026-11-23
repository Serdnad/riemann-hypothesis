module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LocGraded
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.FiniteType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle014
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle067
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
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.isWRing :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R) (h : W.HasOrigin), (∀ s, -2 ≤ W.wt s ∧ W.wt s ≤ 2) → IsWRing W.gr (W.originA h) := by
  classical
  intro O _ _ _ _ R _ _ _ W h hw
  haveI := W.fin
  have hz : ∀ s, W.z s ∈ maximalIdeal R := by
    intro s
    by_contra hs
    have hu : IsUnit (W.z s) := by
      by_contra hn
      exact hs ((IsLocalRing.mem_maximalIdeal _).2 hn)
    have h0 : W.origin h (W.z s) = 0 := by
      simp only [WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
    have hu' := hu.map (W.origin h)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  refine ⟨wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ R W hz, ?_, ?_⟩
  · refine ⟨(Finset.univ.filter (fun i => W.wt i ≠ 0)).image W.zA, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      have hi' : W.wt i ≠ 0 := (Finset.mem_filter.1 hi).2
      have hm : W.zA i ∈ W.gr (W.wt i) := W.z_mem i
      obtain ⟨h1, h2⟩ := hw i
      rcases (show W.wt i = -2 ∨ W.wt i = -1 ∨ W.wt i = 1 ∨ W.wt i = 2 by omega) with e | e | e | e
      · exact Or.inl (e ▸ hm)
      · exact Or.inr (Or.inl (e ▸ hm))
      · exact Or.inr (Or.inr (Or.inl (e ▸ hm)))
      · exact Or.inr (Or.inr (Or.inr (e ▸ hm)))
    · refine top_unique ?_
      rw [← gr_gen O R ℤ W]
      apply Algebra.adjoin_mono
      rintro x (hx | ⟨i, rfl⟩)
      · exact Or.inl hx
      · by_cases hi : W.wt i = 0
        · left
          have hm : W.zA i ∈ W.gr (W.wt i) := W.z_mem i
          rw [hi] at hm
          exact hm
        · right
          simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and]
          exact ⟨i, hi, rfl⟩
  · intro j hj f hf
    obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.1 hf
    have hc : MvPowerSeries.constantCoeff g = 0 := by
      have := hg 0 (by simpa using hj.symm)
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using this
    have hfg : (f : R) = W.π g := hgf.symm
    change W.origin h f.1 = 0
    rw [hfg, WPres.origin_π, hc]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem lc_of_fib {Γ A B : Type} [TopologicalSpace Γ] {f : Γ → A} {g : Γ → B} (hf : IsLocallyConstant f)
    (h : ∀ x y, f x = f y → g x = g y) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_eventually_eq] at hf ⊢
  exact fun x => (hf x).mono fun y hy => h _ _ hy

private theorem exists_grpTop (Γ : Type) [Group Γ] (T : TopologicalSpace Γ) :
    ∃ T' : TopologicalSpace Γ, @IsTopologicalGroup Γ T' _ ∧
      ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ ↔ @IsLocallyConstant Γ M T' φ := by
  classical
  let S := {K : Subgroup Γ // K.Normal ∧ @IsLocallyConstant Γ (Γ ⧸ K) T (fun x => (x : Γ ⧸ K))}
  let ρ : ∀ K : S, Γ →* Equiv.Perm (Γ ⧸ K.1) := fun K => MulAction.toPermHom Γ (Γ ⧸ K.1)
  let T' : TopologicalSpace Γ := ⨅ K : S, TopologicalSpace.induced (ρ K) ⊥
  have htg : ∀ K : S, @IsTopologicalGroup Γ (TopologicalSpace.induced (ρ K) ⊥) _ := by
    intro K
    letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
    haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
    exact topologicalGroup_induced (ρ K)
  refine ⟨T', topologicalGroup_iInf htg, ?_⟩
  intro M _ φ
  have hρT : ∀ K : S, @IsLocallyConstant Γ _ T (ρ K) := by
    intro K
    refine @lc_of_fib Γ _ _ T _ _ K.2.2 ?_
    intro x y hxy
    ext c
    induction c using QuotientGroup.induction_on with
    | H z =>
      simp only [ρ, MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_coe]
      rw [QuotientGroup.eq] at hxy ⊢
      have := K.2.1.conj_mem _ hxy z⁻¹
      simpa [mul_assoc] using this
  have hρT' : ∀ K : S, @IsLocallyConstant Γ _ T' (ρ K) := by
    intro K
    letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
    haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
    rw [@IsLocallyConstant.iff_continuous Γ _ T']
    apply continuous_iInf_dom (i := K)
    exact continuous_induced_dom
  constructor
  · intro hφ
    let K : Subgroup Γ := φ.ker
    have hK : ∀ x y : Γ, (x : Γ ⧸ K) = y ↔ φ x = φ y := by
      intro x y
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul]
      constructor
      · intro e
        calc φ x = φ x * (φ x⁻¹ * φ y) := by rw [e, mul_one]
          _ = φ y := by rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      · intro e
        rw [← e, ← map_mul, inv_mul_cancel, map_one]
    have hmk : @IsLocallyConstant Γ (Γ ⧸ K) T (fun x => (x : Γ ⧸ K)) :=
      @lc_of_fib Γ _ _ T _ _ hφ fun x y e => (hK x y).2 e
    let K' : S := ⟨K, MonoidHom.normal_ker φ, hmk⟩
    refine @lc_of_fib Γ _ _ T' _ _ (hρT' K') ?_
    intro x y hxy
    have := congrArg (fun e : Equiv.Perm (Γ ⧸ K) => e ((1 : Γ) : Γ ⧸ K)) hxy
    simp only [ρ, K', MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_coe, mul_one] at this
    rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one] at this
    exact (hK x y).1 this
  · intro hφ
    have hid : @Continuous Γ Γ T T' id := by
      apply continuous_iInf_rng.2
      intro K
      apply continuous_induced_rng.2
      letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
      haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
      exact (@IsLocallyConstant.iff_continuous Γ _ T _ _ _).1 (hρT K)
    exact @IsLocallyConstant.comp_continuous Γ Γ M T T' φ id hφ hid

private def tr {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [Fintype ι] [DecidableEq ι]
    {rbar : Γ →* Matrix ι ι (ResidueField O)} (T T' : TopologicalSpace Γ)
    (h : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ → @IsLocallyConstant Γ M T' φ)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : @Lift O _ _ Γ ι _ T _ _ rbar R _ _ _) :
    @Lift O _ _ Γ ι _ T' _ _ rbar R _ _ _ :=
  @Lift.mk O _ _ Γ ι _ T' _ _ rbar R _ _ _ (@Lift.hom O _ _ Γ ι _ T _ _ rbar R _ _ _ r)
    (fun a b N => by
      let φ : Γ →* Matrix ι ι (R ⧸ maximalIdeal R ^ N) :=
        (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix.toMonoidHom.comp
          (@Lift.hom O _ _ Γ ι _ T _ _ rbar R _ _ _ r)
      have h1 : @IsLocallyConstant Γ _ T φ := by
        rw [@IsLocallyConstant.iff_eventually_eq Γ _ T]
        intro x
        have h2 := fun a b => (@IsLocallyConstant.iff_eventually_eq Γ _ T _).1
          (@Lift.cont O _ _ Γ ι _ T _ _ rbar R _ _ _ r a b N) x
        have h3 := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => h2 a b
        exact h3.mono fun y hy => Matrix.ext fun a b => hy a b
      exact @lc_of_fib _ _ _ T' _ _ (h _ φ h1) fun x y e => congrFun (congrFun e a) b)
    (@Lift.red O _ _ Γ ι _ T _ _ rbar R _ _ _ r)

theorem UpperTheory.V.Alg.loc_graded_top :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (N : Subgroup Γ) (L : Cond O rbar), Φ.IsLocCond r0.hom N L →
          ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ → ∀ (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsHomog O W.wt (RingHom.ker (p.comp W.π)) →
          ∀ r' : Lift O rbar R', Φ.InH r0.hom R' r' → L R' r' → (∀ s a b, r'.hom s a b ∈ (W.part (w a - w b)).map p.toLinearMap) →
          ∃ r : Lift O rbar R, Φ.InH r0.hom R r ∧ L R r ∧ r.map p = r' ∧ ∀ s a b, r.hom s a b ∈ W.part (w a - w b) := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ h2 Γ _ T rbar r0 hbar hr0 N L hL R _ _ _ R' _ _ _ p hp hker W hz hW r' hr' hLr' hpart
  obtain ⟨U, hU, hiff⟩ : ∃ U : PLift (TopologicalSpace Γ), @IsTopologicalGroup Γ U.down _ ∧
      ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ ↔ @IsLocallyConstant Γ M U.down φ := by
    obtain ⟨T', h1, h2⟩ := exists_grpTop Γ T
    exact ⟨⟨T'⟩, h1, h2⟩
  have hf : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ → @IsLocallyConstant Γ M U.down φ :=
    fun M _ φ => (hiff M φ).1
  have hb : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M U.down φ → @IsLocallyConstant Γ M T φ :=
    fun M _ φ => (hiff M φ).2
  let L' : @Cond O _ _ Γ ι _ U.down _ _ rbar := fun S _ _ _ r => L S (tr U.down T hb r)
  have hL' : @FormData.IsLocCond O _ ι X _ _ _ w Φ _ Γ _ U.down rbar r0.hom N L' := by
    refine @FormData.IsLocCond.mk O _ ι X _ _ _ w Φ _ Γ _ U.down rbar r0.hom N L' ?_ ?_ ?_ ?_ ?_
    · intro S _ _ _ r hr
      obtain ⟨I, hI⟩ := hL.closed S (tr U.down T hb r) hr
      refine ⟨I, fun S' _ _ _ f => ?_⟩
      convert hI S' f using 2
      exact Lift.ext rfl
    · intro S _ _ _ r r2 h hr hh hc hLr
      exact hL.conj S (tr U.down T hb r) (tr U.down T hb r2) h hr hh hc hLr
    · intro S _ _ _ r r2 t hr ht htc hLr
      exact hL.torus S (tr U.down T hb r) (tr U.down T hb r2) t hr ht htc hLr
    · intro S S' _ _ _ _ _ _ q hq hk s hs hLs
      obtain ⟨r1, hr1, hL1, hm1⟩ := hL.lift S S' q hq hk (tr U.down T hb s) hs hLs
      refine ⟨tr T U.down hf r1, hr1, ?_, ?_⟩
      · exact (congrArg (L S) (Lift.ext rfl : tr U.down T hb (tr T U.down hf r1) = r1)).mpr hL1
      · have e := congrArg (@Lift.hom O _ _ Γ ι _ T _ _ rbar S' _ _ _) hm1
        exact Lift.ext e
    · intro S S' _ _ _ _ _ _ q hq hk r1 r2 hr1 hr2 hm hL1
      have e := congrArg (@Lift.hom O _ _ Γ ι _ U.down _ _ rbar S' _ _ _) hm
      exact hL.tangent S S' q hq hk (tr U.down T hb r1) (tr U.down T hb r2) hr1 hr2 (Lift.ext e) hL1
  have hLr'' : L' R' (tr T U.down hf r') := by
    exact (congrArg (L R') (Lift.ext rfl : tr U.down T hb (tr T U.down hf r') = r')).mpr hLr'
  obtain ⟨r, hr, hLr, hmap, hpart'⟩ := @loc_graded O _ _ _ _ ι X _ _ _ _ _ w Φ h2 Γ _ U.down hU rbar
    (tr T U.down hf r0) hbar hr0 N L' hL' R _ _ _ R' _ _ _ p hp hker W hz hW (tr T U.down hf r') hr' hLr'' hpart
  have e := congrArg (@Lift.hom O _ _ Γ ι _ U.down _ _ rbar R' _ _ _) hmap
  exact ⟨tr U.down T hb r, hr, hLr, Lift.ext e, hpart'⟩
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem rel_pres_min {A ι : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Fintype ι]
    (K K0 : Ideal A) (f : ι → A) (h : K = K0 ⊔ Ideal.span (Set.range f)) :
    ∃ s : Finset ι, K = K0 ⊔ Ideal.span (Set.range fun u : s => f u) ∧
      ∀ c : s → A, ∑ u, c u * f u ∈ K0 ⊔ maximalIdeal A * K → ∀ u, c u ∈ maximalIdeal A := by
  classical
  have hex : ∃ n, ∃ s : Finset ι, s.card = n ∧ K = K0 ⊔ Ideal.span (Set.range fun u : s => f u) := by
    refine ⟨_, Finset.univ, rfl, ?_⟩
    rw [h]
    congr 2
    ext x
    simp
  obtain ⟨s, hs, hK⟩ := Nat.find_spec hex
  refine ⟨s, hK, fun c hc u => ?_⟩
  by_contra hu
  have hun : IsUnit (c u) := by
    by_contra h'
    exact hu h'
  obtain ⟨v, hv⟩ := hun
  refine Nat.find_min hex (m := (s.erase u).card) (by rw [← hs]; exact Finset.card_erase_lt_of_mem u.2)
    ⟨s.erase u, rfl, ?_⟩
  set N : Ideal A := K0 ⊔ Ideal.span (Set.range fun w : s.erase u => f w) with hN
  have hmem : ∀ w : s, w ≠ u → f w ∈ N := fun w hw =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨⟨w, Finset.mem_erase.2 ⟨fun e => hw (Subtype.ext e), w.2⟩⟩, rfl⟩)
  have hNK : N ≤ K := by
    rw [hK]
    refine sup_le_sup_left (Ideal.span_mono ?_) _
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨w, Finset.mem_of_mem_erase w.2⟩, rfl⟩
  refine le_antisymm ?_ hNK
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) (IsNoetherian.noetherian K)
    (maximalIdeal_le_jacobson _) ?_
  have h1 : f u ∈ N ⊔ maximalIdeal A • K := by
    have h2 : ∑ w, c w * f w ∈ N ⊔ maximalIdeal A • K :=
      (sup_le_sup_right (le_sup_left : K0 ≤ N) (maximalIdeal A * K)) hc
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)] at h2
    have h3 : ∑ w ∈ Finset.univ.erase u, c w * f w ∈ N ⊔ maximalIdeal A • K :=
      Ideal.mem_sup_left (Ideal.sum_mem _ fun w hw =>
        Ideal.mul_mem_left _ _ (hmem w (Finset.mem_erase.1 hw).1))
    have h4 := Ideal.mul_mem_left _ (↑v⁻¹ : A) (sub_mem h2 h3)
    rwa [add_sub_cancel_right, ← hv, Units.inv_mul_cancel_left] at h4
  conv_lhs => rw [hK]
  refine sup_le (le_sup_of_le_left le_sup_left) (Ideal.span_le.2 ?_)
  rintro _ ⟨w, rfl⟩
  by_cases hw : w = u
  · subst hw; exact h1
  · exact Ideal.mem_sup_left (hmem w hw)

private theorem rel_pres_span_X {O σ : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X s

private theorem rel_pres_max_le {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] {R : Type}
    [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R) (hz : ∀ s, W.z s ∈ maximalIdeal R) :
    maximalIdeal R ≤ Ideal.span (Set.range W.z) ⊔ (maximalIdeal O).map (algebraMap O R) := by
  intro x hx
  obtain ⟨f, rfl⟩ := W.surj x
  have h1 := rel_pres_span_X Finset.univ (f - algebraMap O _ (constantCoeff f)) (fun n hn => by
    have : n = 0 := Finsupp.ext fun i => hn i (Finset.mem_univ i)
    subst this
    simp [MvPowerSeries.algebraMap_apply])
  have h2 : ∀ I : Ideal R, (∀ s, W.z s ∈ I) → W.π f - algebraMap O R (constantCoeff f) ∈ I := by
    intro I hI
    have hle : Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)) ≤ I.comap W.π := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact hI s
    have := hle h1
    rwa [Ideal.mem_comap, map_sub, AlgHom.commutes] at this
  have h3 : algebraMap O R (constantCoeff f) ∈ maximalIdeal R := by
    simpa using sub_mem hx (h2 _ hz)
  have h4 : constantCoeff f ∈ maximalIdeal O := fun hu => h3 (hu.map _)
  have h5 := h2 (Ideal.span (Set.range W.z)) fun s => Ideal.subset_span ⟨s, rfl⟩
  simpa using add_mem (Ideal.mem_sup_left h5)
    (Ideal.mem_sup_right (Ideal.mem_map_of_mem (algebraMap O R) h4))

theorem UpperTheory.V.Alg.rel_pres :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (WB : WPres O X B) (W₀ : WPres O X R) (i : B →ₐ[O] R), (∀ s, WB.z s ∈ maximalIdeal B) → (∀ s, W₀.z s ∈ maximalIdeal R) → (∀ s, i (WB.z s) ∈ W₀.part (WB.wt s)) →
      ∀ (τ : Type) [Fintype τ] (z : τ → R) (wt : τ → X), (∀ t, z t ∈ maximalIdeal R ∧ z t ∈ W₀.part (wt t)) →
      maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
      ∃ (W : WPres O X R) (κ : Type) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ) (f : κ → MvPowerSeries W.σ O) (wf : κ → X), IsRelPres WB i W e f wf ∧
        (∀ t, W.z (e (.inr t)) = z t ∧ W.wt (e (.inr t)) = wt t) ∧ (∀ j, W.part j = W₀.part j) ∧
        ∀ c : κ → O, ∑ u, c u • f u ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) ⊔ maximalIdeal (MvPowerSeries W.σ O) * RingHom.ker W.π → ∀ u, c u ∈ maximalIdeal O := by
  intro O _ _ _ _ X _ _ _ B _ _ _ R _ _ _ WB W₀ i hB h0 hi τ _ z wt hz hgen
  classical
  have him : ∀ s, i (WB.z s) ∈ maximalIdeal R := fun s => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hB s
  have hz' : ∀ s : WB.σ ⊕ τ, Sum.elim (fun s => i (WB.z s)) z s ∈ maximalIdeal R ∧
      Sum.elim (fun s => i (WB.z s)) z s ∈ W₀.part (Sum.elim WB.wt wt s) := by
    rintro (s | t)
    · exact ⟨him s, hi s⟩
    · exact hz t
  obtain ⟨W, e, he⟩ := pres_new O X R W₀ h0 (WB.σ ⊕ τ) (Sum.elim WB.wt wt) (Sum.elim (fun s => i (WB.z s)) z) hz'
    (hgen.trans (sup_le_sup_right (sup_le (le_sup_of_le_left (Ideal.span_mono (by
      rintro _ ⟨t, rfl⟩
      exact ⟨.inr t, rfl⟩))) (by
        refine (Ideal.map_mono (rel_pres_max_le WB hB)).trans ?_
        rw [Ideal.map_sup]
        refine sup_le_sup ?_ ?_
        · rw [Ideal.map_span]
          refine Ideal.span_mono ?_
          rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
          exact ⟨.inl s, rfl⟩
        · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
          intro c hc
          rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
          exact Ideal.mem_map_of_mem _ hc)) _))
  have hW : ∀ s, W.z s ∈ maximalIdeal R ∧ W.z s ∈ W₀.part (W.wt s) := fun s => by
    obtain ⟨s, rfl⟩ := e.surjective s
    rw [(he s).1, (he s).2]
    exact hz' s
  have hpart := pres_indep O X R W₀ h0 W (fun s => (hW s).1) fun s => (hW s).2
  have hcomm : W.π.comp (MvPowerSeries.rename fun s => e (.inl s)) = i.comp WB.π := by
    refine (co_ev O O R WB.σ (Algebra.ofId _ _) _ him).unique ⟨fun x => ?_, fun s => ?_⟩ ⟨fun x => ?_, fun s => rfl⟩
    · exact AlgHom.commutes _ x
    · rw [AlgHom.comp_apply, rename_X]
      exact (he (.inl s)).1
    · exact AlgHom.commutes _ x
  have hcomm' : ∀ x, W.π (MvPowerSeries.rename (fun s => e (.inl s)) x) = i (WB.π x) :=
    fun x => AlgHom.congr_fun hcomm x
  haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ
  obtain ⟨n, g, c, hg, hK⟩ := ker_gen O X W.σ W.wt _ W.homog
  have hle : (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) ≤ RingHom.ker W.π := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomm', (RingHom.mem_ker).1 hx, map_zero]
  obtain ⟨s, hs, hmin⟩ := rel_pres_min (RingHom.ker W.π)
    ((RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s))) g (by rw [← hK, sup_eq_right.2 hle])
  refine ⟨W, s, inferInstance, e, fun u => g u, fun u => c u, ⟨fun s => (he (.inl s)).2, hcomm', fun u => hg u, hs⟩,
    fun t => he (.inr t), hpart, fun a ha u hu => ?_⟩
  refine hmin (fun u => algebraMap O _ (a u)) ?_ u (hu.map _)
  simpa only [Algebra.smul_def] using ha
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.gr_noeth :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsNoetherianRing W.A ∧ Algebra.FiniteType (W.gr 0) W.A ∧ ∀ j, ∃ s : Finset W.A, (∀ a ∈ s, a ∈ W.gr j) ∧ W.gr j = W.gr 0 * Submodule.span O (s : Set W.A) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz
  classical
  haveI := W.fin
  haveI hco : IsCO O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal O X R W hz
  haveI : IsNoetherianRing (W.gr 0) := IsCO.toIsNoetherian O
  have hgen : Algebra.adjoin (W.gr 0) (Set.range W.zA) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    have ha : a ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      rw [gr_gen O R X W]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · have e : algebraMap (W.gr 0) W.A ⟨x, hx⟩ = x := rfl
        rw [← e]
        exact Subalgebra.algebraMap_mem _ _
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r =>
      have hr : algebraMap O W.A r ∈ W.gr 0 := SetLike.algebraMap_mem_graded W.gr r
      have e : algebraMap (W.gr 0) W.A ⟨_, hr⟩ = algebraMap O W.A r := rfl
      rw [← e]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  haveI hft : Algebra.FiniteType (W.gr 0) W.A :=
    ⟨⟨Finset.univ.image W.zA, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgen]⟩⟩
  refine ⟨Algebra.FiniteType.isNoetherianRing (W.gr 0) W.A, hft, ?_⟩
  intro j
  have hmono : ∀ m : W.σ →₀ ℕ, monomial m (1 : O) ∈ wtPart O W.wt (Finsupp.weight W.wt m) := by
    intro m n hn
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact hn rfl
  obtain ⟨μ, hμS, hμ⟩ := part_span O R X W {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)
  let mA : (W.σ →₀ ℕ) → W.A := fun m =>
    ⟨W.π (monomial m 1), W.part_le_A (Submodule.mem_map_of_mem (hmono m))⟩
  have hsj : ∀ a ∈ μ.image mA, a ∈ W.gr j := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hw : Finsupp.weight W.wt m = j := hμS hm
    show (W.π (monomial m 1) : R) ∈ W.part j
    rw [← hw]
    exact Submodule.mem_map_of_mem (hmono m)
  refine ⟨μ.image mA, hsj, ?_⟩
  apply le_antisymm
  · intro a ha
    have ha' : (a : R) ∈ W.part j := ha
    obtain ⟨f, hf, hfa⟩ := Submodule.mem_map.mp ha'
    obtain ⟨b, hb, hfb⟩ := hμ f (fun n hn => hf n hn)
    let bA : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (b m), W.part_le_A (Submodule.mem_map_of_mem (hb m))⟩
    have hsum : a = ∑ m ∈ μ, bA m * mA m := by
      apply Subtype.ext
      rw [← hfa]

      simp [hfb, map_sum, map_mul, bA, mA]
    rw [hsum]
    refine Submodule.sum_mem _ fun m hm => Submodule.mul_mem_mul ?_ ?_
    · show (W.π (b m) : R) ∈ W.part 0
      exact Submodule.mem_map_of_mem (hb m)
    · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mA hm))
  · rw [Submodule.mul_le]
    intro x hx y hy
    have hy' : y ∈ W.gr j := (Submodule.span_le.mpr fun z hz => hsj z hz) hy
    simpa using SetLike.GradedMul.mul_mem hx hy'
end
