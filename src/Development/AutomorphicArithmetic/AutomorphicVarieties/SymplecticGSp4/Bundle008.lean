module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x => continuous_inv.smul continuous_const
  have hc : ContAction (permR (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 := continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (Z1 (permR (ZMod n) H)) := by
    have hB : Finite (B1 (permR (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((B1 (permR (ZMod n) H)).comap (Z1 (permR (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permR (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ := fun φ hφ =>
    continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → Z1 (permR (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

private theorem fin_above {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((n : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_span_singleton]; exact hv

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.phiGam :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → CohomologyHyp → PhiCond D.Gam l := by
  intro Ω _ _ _ l hl c D hD hP
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfin : D.SP.Finite := by
    refine (D.S.finite_toSet.biUnion fun p hp => fin_above (hD.S_prime p hp).ne_zero).subset ?_
    rintro v ⟨p, hp, hv⟩
    exact Set.mem_biUnion hp hv
  have hS : ContainsAbove hfin.toFinset l := fun v hv => hfin.mem_toFinset.2 ⟨l, hD.l_mem, hv⟩
  haveI hK : CompactSpace (GS Ω (hfin.toFinset : Set (HeightOneSpectrum (𝓞 ℚ)))) := inferInstance
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (GS Ω (hfin.toFinset : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) :=
    phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
      obtain ⟨-, f1, -⟩ := hP.gf ℚ Ω l 1 M hfin.toFinset ρ one_pos hS hρ
      exact f1
  rw [pow_one, hfin.coe_toFinset] at key
  exact key
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem wcomp_mul_homog (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) (G : MvPowerSeries σ O) (j : X) :
    wcomp O wt j (G * e) = wcomp O wt (j - w) G * e := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [he _ h2, mul_zero, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      apply h
      rw [← hp', map_add (f := _), h1, h2, sub_add_cancel]
    · rw [he _ h2, mul_zero]

private theorem span_coeffs {O R X κ N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    (W : WPres O X R) [Fintype κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i)) (u : N → X)
    (B : Submodule O R) (hB : ∀ n i, W.part (u n - c i) ≤ B) (x : R) (hx' : x ∈ ⨆ n, W.part (u n))
    (hx : x ∈ Ideal.span (Set.range g)) : ∃ a : κ → R, (∀ i, a i ∈ B) ∧ x = ∑ i, a i * g i := by
  classical
  have hg' : ∀ i, ∃ e ∈ wtPart O W.wt (c i), W.π e = g i := fun i => hg i
  choose e he heg using hg'
  have hl : ∃ f, W.π f = x ∧ ∃ s : Finset X, (∀ j ∈ s, ∃ n, u n = j) ∧
      ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0 := by
    refine Submodule.iSup_induction (fun n => W.part (u n))
      (motive := fun z : R => ∃ f, W.π f = z ∧ ∃ s : Finset X, (∀ j ∈ s, ∃ n, u n = j) ∧
        ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0) hx' ?_ ?_ ?_
    · rintro i _ ⟨f, hf, rfl⟩
      exact ⟨f, rfl, {u i}, fun j hj => ⟨i, (Finset.mem_singleton.1 hj).symm⟩,
        fun n hn => hf n (by simpa using hn)⟩
    · exact ⟨0, map_zero _, ∅, by simp, fun n _ => map_zero _⟩
    · rintro a b ⟨f, hf, s, ht, hs⟩ ⟨f', hf', s', ht', hs'⟩
      refine ⟨f + f', by rw [map_add (f := _), hf, hf'], s ∪ s', fun j hj => ?_, fun n hn => ?_⟩
      · rcases Finset.mem_union.1 hj with h | h
        · exact ht j h
        · exact ht' j h
      · rw [Finset.mem_union, not_or] at hn
        rw [map_add (f := _), hs n hn.1, hs' n hn.2, add_zero]
  obtain ⟨f, hf, s, ht, hs⟩ := hl
  have hsum : f = ∑ j ∈ s, wcomp O W.wt j f := by
    ext n

    rw [map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · exact hs n h
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
  choose G hG using fun i => W.surj (a i)
  have h1 : f - ∑ i, G i * e i ∈ RingHom.ker W.π := by

    rw [RingHom.mem_ker, map_sub, hf, ← ha, map_sum]
    simp [hG, heg]
  have key : ∀ j, W.π (wcomp O W.wt j f) = ∑ i, W.π (wcomp O W.wt (j - c i) (G i)) * g i := by
    intro j
    have h2 := W.homog _ h1 j

    rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wcomp_mul_homog O W.wt (he i), map_mul, heg]
  refine ⟨fun i => ∑ j ∈ s, W.π (wcomp O W.wt (j - c i) (G i)), fun i => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j hj => ?_
    obtain ⟨n, rfl⟩ := ht j hj
    exact hB n i ⟨_, wcomp_mem O W.wt _ _, rfl⟩
  · rw [← hf]
    conv_lhs => rw [hsum]

    rw [map_sum]
    simp only [key, Finset.sum_mul]
    exact Finset.sum_comm

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.kerA :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, (∀ f : M.A, M.toSS f = 0 ↔ f ∈ M.eqns.ideal) ∧ (∀ n (x : M.SS), x.1 ∈ M.sPart (0, n) → ∃ f ∈ M.gr n, M.toSS f = x) ∧ ∀ n, ∀ f ∈ M.gr n, (M.toSS f).1 ∈ M.sPart (0, n) := by
  intro Ω _ _ _ l _ c D _ M
  refine ⟨fun f => ⟨fun hf => ?_, fun hf => ?_⟩, ?_, ?_⟩
  · have h0 : (f : M.R) ∈ RingHom.ker M.π := congrArg Subtype.val hf
    rw [M.ker, ← Set.Sum.elim_range, ← Set.Sum.elim_range] at h0
    obtain ⟨a, ha, hfa⟩ := span_coeffs M.W (Sum.elim (Sum.elim M.F M.E) M.Z)
      (fun i => ((0 : ℤ), Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => 1)) (fun _ => 0) i))
      (by
        rintro ((i | i) | i)
        · exact M.hF i
        · exact M.hE i
        · exact (M.hZ i).1)
      (fun n : ℤ => ((0 : ℤ), n)) (Subalgebra.toSubmodule M.A)
      (fun n i x hx => M.aPart_le (n := n - Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => 1)) (fun _ => 0) i)
        (by simpa [Model.aPart] using hx))
      f f.2 h0
    have hf' : f = ∑ i, (⟨a i, ha i⟩ : M.A) * Sum.elim (Sum.elim M.eqns.F M.eqns.E) M.eqns.Z i := by
      apply Subtype.ext
      rw [hfa, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl ?_
      rintro ((i | i) | i) - <;> rfl
    rw [hf']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    rcases i with (i | i) | i
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))
    · exact Or.inr ⟨i, rfl⟩
  · have hle : M.eqns.ideal ≤ RingHom.ker M.toSS := by
      refine Ideal.span_le.2 fun x hx => ?_
      have hk : (x : M.R) ∈ RingHom.ker M.π := by
        rw [M.ker]
        refine Ideal.subset_span ?_
        rcases hx with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
        · exact Or.inl (Or.inl ⟨i, rfl⟩)
        · exact i.elim0
        · exact Or.inl (Or.inr ⟨i, rfl⟩)
        · exact i.elim0
        · exact Or.inr ⟨i, rfl⟩
      exact Subtype.ext hk
    exact hle hf
  · rintro n x ⟨f, hf, hfx⟩
    exact ⟨⟨f, M.aPart_le (n := n) hf⟩, hf, Subtype.ext hfx⟩
  · intro n f hf
    exact ⟨f, hf, rfl⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem part_indep {O X R : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R]
    (W : WPres O X R) : iSupIndep W.part := by
  have h := (W.A.val.toLinearMap.iSupIndep_map Subtype.val_injective
    (gr_internal O X R W).submodule_iSupIndep)
  convert h using 1
  funext j
  rw [WPres.gr, Submodule.map_comap_eq, eq_comm, inf_eq_right]
  intro x hx
  exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩

private theorem part_gen {O X R : Type} [CommRing O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [CommRing R] [Algebra O R] (W : WPres O X R) :
    Algebra.adjoin O ((W.part 0 : Set R) ∪ Set.range W.z) = W.A := by
  have h := congrArg (Subalgebra.map W.A.val) (gr_gen O R X W)
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val] at h
  rw [← h]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    constructor
    · intro hx
      exact ⟨⟨x, W.part_le_A hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · ext x
    simp [WPres.zA, WPres.z]

private theorem quot_pres {O X R S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing S] [Algebra O S] [IsCO O S] (W : WPres O X R) (org : W.HasOrigin) (π : R →ₐ[O] S)
    (surj : Function.Surjective π) {κ : Type} [Finite κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i))
    (ker : RingHom.ker π = Ideal.span (Set.range g)) :
    ∃ WS : WPres O X S, (∀ w, WS.part w = (W.part w).map π.toLinearMap) ∧ ∀ i, WS.z i ∈ maximalIdeal S := by
  have hz : ∀ i, W.z i ∈ maximalIdeal R := by
    intro i
    let ψ : R →+* ResidueField O := (IsLocalRing.residue O).comp (W.origin org).toRingHom
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨algebraMap O R a, by simp [ψ]⟩
    have heq : RingHom.ker ψ = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
    rw [← heq, RingHom.mem_ker]
    simp [ψ, WPres.z, WPres.origin_π]
  have hhom : IsHomog O W.wt (RingHom.ker (π.comp W.π)) := by
    have h := (homog_span O R X W κ (fun i => ⟨g i, W.part_le_A (hg i)⟩) c
      (fun i => Submodule.mem_comap.mpr (hg i))).1
    convert h using 1
    ext f
    rw [RingHom.mem_ker, Ideal.mem_comap]
    show π (W.π f) = 0 ↔ W.π f ∈ Ideal.span (Set.range g)
    rw [← ker, RingHom.mem_ker]
  refine ⟨W.quot π surj hhom, ?_, ?_⟩
  · intro w
    exact Submodule.map_comp W.π.toLinearMap π.toLinearMap (wtPart O W.wt w)
  · intro i
    show π (W.z i) ∈ maximalIdeal S
    rw [← res_eq_zero_iff O S, res_map, res_eq_zero_iff]
    exact hz i

theorem UpperTheory.V.GradeZeroInterpolatingElement.sInternal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, iSupIndep M.sPart ∧ (∃ s : Finset M.S, (∀ x ∈ s, ∃ w, x ∈ M.sPart w) ∧ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ s) = M.SS) ∧ ∃ WS : WPres c.O (ℤ × ℤ) M.S, (∀ w, WS.part w = M.sPart w) ∧ ∀ i, WS.z i ∈ maximalIdeal M.S := by
  intro Ω _ _ _ l _ c D _ M
  classical
  let g : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → M.R := Sum.elim M.F (Sum.elim M.E M.Z)
  let cw : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → ℤ × ℤ :=
    Sum.elim (fun _ => -wPs) (Sum.elim (fun _ => wPs) (fun _ => 0))
  have hg : ∀ i, g i ∈ M.W.part (cw i) := by
    rintro (i | i | i)
    · exact M.hF i
    · exact M.hE i
    · exact (M.hZ i).1
  have hker : RingHom.ker M.π = Ideal.span (Set.range g) := by
    rw [M.ker]
    simp only [g, Set.Sum.elim_range, Set.union_assoc]
  obtain ⟨WS, hpart, hzm⟩ := quot_pres M.W M.org M.π M.surj g cw hg hker
  have hp : WS.part = M.sPart := funext hpart
  have hA : WS.A = M.SS := by
    unfold WPres.A Model.SS
    congr
  haveI := WS.fin
  refine ⟨by rw [← hp]; exact part_indep WS, ⟨Finset.univ.image WS.z, ?_, ?_⟩, WS, hpart, hzm⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨WS.wt i, by rw [← hp]; exact WS.z_mem i⟩
  · rw [← hA, ← part_gen WS, ← hp]
    congr 2
    simp
end
