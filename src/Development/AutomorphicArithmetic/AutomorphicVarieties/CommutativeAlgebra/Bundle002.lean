module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle001
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem complete_of_pow {R : Type} [CommRing R] (I : Ideal R) (N : ℕ) (h : I ^ N = ⊥) :
    IsAdicComplete I R := by
  have hb : (I ^ N • ⊤ : Submodule R R) = ⊥ := by rw [h, Submodule.bot_smul]
  have key : ∀ x y : R, x ≡ y [SMOD (I ^ N • ⊤ : Submodule R R)] → x = y := by
    intro x y hxy
    rw [hb, SModEq.sub_mem, Submodule.mem_bot, sub_eq_zero] at hxy
    exact hxy
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    exact key x 0 (hx N)
  · intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · have e := key _ _ (hf hn)
      rw [SModEq.sub_mem, e, sub_self]
      exact Submodule.zero_mem _

private theorem mk_inj {R : Type} [CommRing R] (I : Ideal R) (h : I = ⊥) :
    Function.Injective (Ideal.Quotient.mk I) := by
  subst h
  intro x y hxy
  rw [Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at hxy
  exact hxy

private theorem finite_of_pow (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (N : ℕ) (h : maximalIdeal A ^ N = ⊥) : Finite A := by
  haveI : Finite (ResidueField A) := Finite.of_surjective _ (resMap_bijective O A).2
  haveI : Finite (A ⧸ maximalIdeal A) := this
  haveI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal A)) N
  exact Finite.of_injective _ (mk_inj _ h)

private theorem sub_co (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (N : ℕ)
    (A₁ : Type) [CommRing A₁] [Algebra O A₁] [IsCO O A₁] (A₂ : Type) [CommRing A₂] [Algebra O A₂] [IsCO O A₂]
    (h₁ : maximalIdeal A₁ ^ N = ⊥) (h₂ : maximalIdeal A₂ ^ N = ⊥) (B : Type) [CommRing B] [Algebra O B]
    (p₁ : B →ₐ[O] A₁) (p₂ : B →ₐ[O] A₂) (hinj : ∀ x y, p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hres : ∀ x, res O A₁ (p₁ x) = res O A₂ (p₂ x)) :
    ∃ _ : IsCO O B, maximalIdeal B ^ N = ⊥ := by
  classical
  haveI : Finite A₁ := finite_of_pow O A₁ N h₁
  haveI : Finite A₂ := finite_of_pow O A₂ N h₂
  have hinj' : Function.Injective (fun x : B => (p₁ x, p₂ x)) := fun x y hxy =>
    hinj x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  haveI : Finite B := Finite.of_injective _ hinj'
  let φ : B →ₐ[O] ResidueField O := (res O A₁).comp p₁
  have hφ1 : ∀ x, φ x = res O A₁ (p₁ x) := fun x => rfl
  have hφ2 : ∀ x, φ x = res O A₂ (p₂ x) := fun x => hres x
  have hunit : ∀ x : B, φ x ≠ 0 → IsUnit x := by
    intro x hx
    have u1 : IsUnit (p₁ x) := by
      by_contra hn
      apply hx
      rw [hφ1, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    have u2 : IsUnit (p₂ x) := by
      by_contra hn
      apply hx
      rw [hφ2, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    have hmul : Function.Injective (fun y : B => x * y) := by
      intro y z hyz
      have e1 := congrArg p₁ hyz
      have e2 := congrArg p₂ hyz
      simp only [map_mul] at e1 e2
      exact hinj y z (u1.mul_left_cancel e1) (u2.mul_left_cancel e2)
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hmul) 1
    have hy' : x * y = 1 := hy
    exact ⟨⟨x, y, hy', by rw [mul_comm]; exact hy'⟩, rfl⟩
  have hnon : ∀ x : B, IsUnit x → φ x ≠ 0 := fun x hx => (hx.map φ).ne_zero
  haveI : Nontrivial B := ⟨⟨0, 1, fun h01 => by
    have e := congrArg φ h01
    rw [map_zero, map_one] at e
    exact zero_ne_one e⟩⟩
  haveI : IsLocalRing B := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases ha : φ a = 0
    · right
      apply hunit
      rw [map_sub, map_one, ha, sub_zero]
      exact one_ne_zero
    · left
      exact hunit a ha
  have hmax : ∀ x : B, x ∈ maximalIdeal B ↔ φ x = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx
      by_contra hne
      exact hx (hunit x hne)
    · intro hx hu
      exact hnon x hu hx
  haveI : IsNoetherian B B := inferInstance
  have hpow : maximalIdeal B ^ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_bot]
    have m1 : Ideal.map p₁ (maximalIdeal B) ≤ maximalIdeal A₁ := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, ← res_eq_zero_iff O, ← hφ1]
      exact (hmax y).mp hy
    have m2 : Ideal.map p₂ (maximalIdeal B) ≤ maximalIdeal A₂ := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, ← res_eq_zero_iff O, ← hφ2]
      exact (hmax y).mp hy
    have x1 : p₁ x ∈ maximalIdeal A₁ ^ N := by
      apply pow_le_pow_left' m1 N
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem p₁ hx
    have x2 : p₂ x ∈ maximalIdeal A₂ ^ N := by
      apply pow_le_pow_left' m2 N
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem p₂ hx
    rw [h₁, Ideal.mem_bot] at x1
    rw [h₂, Ideal.mem_bot] at x2
    exact hinj x 0 (by rw [x1, map_zero]) (by rw [x2, map_zero])
  refine ⟨{ complete := complete_of_pow _ N hpow, isLocalHom := ⟨fun a ha => ?_⟩, res_surj := fun x => ?_ }, hpow⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, ← AlgHom.commutes φ]
    exact hnon _ ha
  · obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (φ x)
    refine ⟨a, (hmax _).mpr ?_⟩
    rw [map_sub, AlgHom.commutes, ResidueField.algebraMap_eq, ha, sub_self]

theorem UpperTheory.exists_lift_dominating_pair_of_maximalIdeal_pow_eq_bot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (N : ℕ) (A₁ : Type) [CommRing A₁] [Algebra O A₁] [IsCO O A₁] (A₂ : Type) [CommRing A₂] [Algebra O A₂] [IsCO O A₂] (r₁ : Lift O rbar A₁) (r₂ : Lift O rbar A₂), maximalIdeal A₁ ^ N = ⊥ → maximalIdeal A₂ ^ N = ⊥ →
          ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (_ : IsCO O B) (r : Lift O rbar B) (p₁ : B →ₐ[O] A₁) (p₂ : B →ₐ[O] A₂), maximalIdeal B ^ N = ⊥ ∧ Algebra.adjoin O {x : B | ∃ g a b, x = r.hom g a b} = ⊤ ∧ r.map p₁ = r₁ ∧ r.map p₂ = r₂ := by
  intro O _ _ _ Γ ι _ _ _ _ rbar N A₁ _ _ _ A₂ _ _ _ r₁ r₂ h₁ h₂
  classical
  let gen : Set (A₁ × A₂) := {x | ∃ g a b, x = (r₁.hom g a b, r₂.hom g a b)}
  let S : Subalgebra O (A₁ × A₂) := Algebra.adjoin O gen
  let p₁ : S →ₐ[O] A₁ := (AlgHom.fst O A₁ A₂).comp S.val
  let p₂ : S →ₐ[O] A₂ := (AlgHom.snd O A₁ A₂).comp S.val
  have hinj : ∀ x y : S, p₁ x = p₁ y → p₂ x = p₂ y → x = y := fun x y e1 e2 =>
    Subtype.ext (Prod.ext e1 e2)
  have hle : S ≤ AlgHom.equalizer ((res O A₁).comp (AlgHom.fst O A₁ A₂))
      ((res O A₂).comp (AlgHom.snd O A₁ A₂)) := by
    apply Algebra.adjoin_le
    rintro x ⟨g, a, b, rfl⟩
    rw [SetLike.mem_coe, AlgHom.mem_equalizer]
    show res O A₁ (r₁.hom g a b) = res O A₂ (r₂.hom g a b)
    exact (r₁.red g a b).trans (r₂.red g a b).symm
  have hres : ∀ x : S, res O A₁ (p₁ x) = res O A₂ (p₂ x) := fun x =>
    (AlgHom.mem_equalizer _ _ _).mp (hle x.2)
  obtain ⟨hCO, hpow⟩ := sub_co O N A₁ A₂ h₁ h₂ S p₁ p₂ hinj hres
  haveI := hCO
  let M : Γ → Matrix ι ι S := fun g => Matrix.of fun a b =>
    ⟨(r₁.hom g a b, r₂.hom g a b), Algebra.subset_adjoin ⟨g, a, b, rfl⟩⟩
  have hMv : ∀ g a b, ((M g a b : S) : A₁ × A₂) = (r₁.hom g a b, r₂.hom g a b) := fun _ _ _ => rfl
  let hom : Γ →* Matrix ι ι S :=
    { toFun := M
      map_one' := by
        refine Matrix.ext fun a b => Subtype.ext ?_
        rw [hMv, map_one r₁.hom, map_one r₂.hom]
        by_cases hab : a = b
        · subst hab
          simp
        · simp [Matrix.one_apply_ne hab]
      map_mul' := by
        intro g h
        refine Matrix.ext fun a b => Subtype.ext ?_
        rw [hMv, map_mul r₁.hom, map_mul r₂.hom, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
        show _ = S.val (∑ c, M g a c * M h c b)

        rw [map_sum]
        simp only [map_mul]
        change _ = ∑ c, ((M g a c : A₁ × A₂) * (M h c b : A₁ × A₂))
        simp only [hMv]
        ext <;> simp [Prod.fst_sum, Prod.snd_sum] }
  have hloc : ∀ a b, IsLocallyConstant fun g => M g a b := by
    intro a b
    have l1 : IsLocallyConstant fun g => r₁.hom g a b :=
      IsLocallyConstant.desc _ _ (r₁.cont a b N) (mk_inj _ h₁)
    have l2 : IsLocallyConstant fun g => r₂.hom g a b :=
      IsLocallyConstant.desc _ _ (r₂.cont a b N) (mk_inj _ h₂)
    exact IsLocallyConstant.desc _ (Subtype.val : S → A₁ × A₂) (l1.prodMk l2) Subtype.val_injective
  let r : Lift O rbar S :=
    { hom := hom
      cont := fun a b n => (hloc a b).comp _
      red := fun g a b => by
        rw [← res_map p₁]
        exact r₁.red g a b }
  refine ⟨S, inferInstance, inferInstance, hCO, r, p₁, p₂, hpow, ?_, ?_, ?_⟩
  · apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨g, a, b, rfl⟩, rfl⟩
      exact ⟨g, a, b, rfl⟩
    · rintro ⟨g, a, b, rfl⟩
      exact ⟨M g a b, ⟨g, a, b, rfl⟩, rfl⟩
  · exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => rfl)
  · exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => rfl)
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

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

theorem UpperTheory.V.Alg.homog_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] (W : WPres O X R) (κ : Type) [Finite κ] (g : κ → W.A) (c : κ → X), (∀ i, g i ∈ W.gr (c i)) →
      IsHomog O W.wt ((Ideal.span (Set.range fun i => (g i : R))).comap W.π) ∧
      ∀ x : W.A, (x : R) ∈ Ideal.span (Set.range fun i => (g i : R)) ↔ x ∈ Ideal.span (Set.range g) := by
  intro O R _ _ _ X _ W κ _ g c hg
  classical
  cases nonempty_fintype κ
  have hback : ∀ x : W.A, x ∈ Ideal.span (Set.range g) →
      (x : R) ∈ Ideal.span (Set.range fun i => (g i : R)) := by
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => (a i : R), ?_⟩
    rw [← ha]
    simp
  have hg' : ∀ i, ∃ e ∈ wtPart O W.wt (c i), W.π e = (g i : R) := fun i => hg i
  choose e he heg using hg'
  have key : ∀ f, W.π f ∈ Ideal.span (Set.range fun i => (g i : R)) → ∀ j,
      ∃ y ∈ Ideal.span (Set.range g), (y : R) = W.π (wcomp O W.wt j f) := by
    intro f hf j
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
    choose G hG using fun i => W.surj (a i)
    have h1 : f - ∑ i, G i * e i ∈ RingHom.ker W.π := by

      rw [RingHom.mem_ker, map_sub, ← ha, map_sum]
      simp [hG, heg]
    have h2 := W.homog _ h1 j

    rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h2
    have hm : ∀ i, W.π (wcomp O W.wt (j - c i) (G i)) ∈ W.A := fun i =>
      W.part_le_A (j := j - c i) ⟨_, wcomp_mem O W.wt _ _, rfl⟩
    refine ⟨∑ i, ⟨_, hm i⟩ * g i, Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => ⟨_, hm i⟩, rfl⟩, ?_⟩
    rw [h2, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wcomp_mul_homog O W.wt (he i), map_mul, heg]
    rfl
  refine ⟨fun f hf j => ?_, fun x => ⟨fun hx => ?_, hback x⟩⟩
  · obtain ⟨y, hy, hy'⟩ := key f hf j
    rw [Ideal.mem_comap, ← hy']
    exact hback y hy
  · have hx' : (x : R) ∈ ⨆ j, W.part j := x.2
    have hl : ∃ f, W.π f = (x : R) ∧ ∃ s : Finset X, ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0 := by
      refine Submodule.iSup_induction W.part
        (motive := fun z : R => ∃ f, W.π f = z ∧
          ∃ s : Finset X, ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0) hx' ?_ ?_ ?_
      · rintro i _ ⟨f, hf, rfl⟩
        exact ⟨f, rfl, {i}, fun n hn => hf n (by simpa using hn)⟩
      · exact ⟨0, map_zero _, ∅, fun n _ => map_zero _⟩
      · rintro a b ⟨f, hf, s, hs⟩ ⟨f', hf', s', hs'⟩
        refine ⟨f + f', by rw [map_add (f := _), hf, hf'], s ∪ s', fun n hn => ?_⟩
        rw [Finset.mem_union, not_or] at hn
        rw [map_add (f := _), hs n hn.1, hs' n hn.2, add_zero]
    obtain ⟨f, hf, s, hs⟩ := hl
    have hsum : f = ∑ j ∈ s, wcomp O W.wt j f := by
      ext n

      rw [map_sum]
      simp only [coeff_wcomp]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · exact hs n h
    choose y hy hy' using key f (hf ▸ hx)
    have : x = ∑ j ∈ s, y j := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, ← hf]
      conv_lhs => rw [hsum]

      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (hy' j).symm
    rw [this]
    exact Ideal.sum_mem _ fun j _ => hy j
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.gr_internal :
    ∀ (O X R : Type) [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R), DirectSum.IsInternal W.gr := by
  intro O X R _ _ _ _ _ W
  have hhom := W.homog
  unfold IsHomog at hhom
  have hK : ∀ (j : X) (f g : MvPowerSeries W.σ O), W.π f = W.π g →
      W.π (wcomp O W.wt j f) = W.π (wcomp O W.wt j g) := by
    intro j f g hfg
    have hker : f - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker]
      simp [hfg]
    have h2 := hhom (f - g) hker j
    rw [RingHom.mem_ker] at h2
    simp only [map_sub] at h2
    exact sub_eq_zero.mp (by simpa using h2)
  have hself : ∀ (j : X) (f : MvPowerSeries W.σ O), f ∈ wtPart O W.wt j →
      wcomp O W.wt j f = f := by
    intro j f hf
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hf n h).symm
  have hoff : ∀ (i j : X) (f : MvPowerSeries W.σ O), f ∈ wtPart O W.wt i → i ≠ j →
      wcomp O W.wt j f = 0 := by
    intro i j f hf hij
    ext n
    rw [coeff_wcomp, map_zero]
    split_ifs with h
    · exact hf n (fun h' => hij (h'.symm.trans h))
    · rfl
  have hgr : ∀ (i : X) (y : W.A), y ∈ W.gr i ↔ y.1 ∈ W.part i := fun i y => Iff.rfl
  have hpart : ∀ (i : X) (x : R), x ∈ W.part i ↔ ∃ f ∈ wtPart O W.wt i, W.π f = x := by
    intro i x
    exact Submodule.mem_map
  let T : X → Submodule O W.A := fun j =>
    { carrier := {y | ∀ f, W.π f = y.1 → W.π (wcomp O W.wt j f) = 0}
      add_mem' := by
        intro a b ha hb f hf
        obtain ⟨fa, hfa⟩ := W.surj a.1
        obtain ⟨fb, hfb⟩ := W.surj b.1
        have e : W.π f = W.π (fa + fb) := by
          rw [hf, map_add (f := _), hfa, hfb]
          rfl
        rw [hK j f (fa + fb) e, map_add (f := _), map_add (f := _), ha fa hfa, hb fb hfb, add_zero]
      zero_mem' := by
        intro f hf
        have e : W.π f = W.π 0 := by
          rw [hf, map_zero]
          rfl
        rw [hK j f 0 e, map_zero, map_zero]
      smul_mem' := by
        intro c a ha f hf
        obtain ⟨fa, hfa⟩ := W.surj a.1
        have e : W.π f = W.π (c • fa) := by
          rw [hf, map_smul, hfa]
          rfl
        rw [hK j f (c • fa) e, map_smul, map_smul, ha fa hfa, smul_zero] }
  have hT : ∀ (i j : X), i ≠ j → W.gr i ≤ T j := by
    intro i j hij y hy f hf
    obtain ⟨g, hg, hgy⟩ := (hpart i y.1).mp ((hgr i y).mp hy)
    rw [hK j f g (hf.trans hgy.symm), hoff i j g hg hij, map_zero]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro j
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hle : (⨆ i, ⨆ (_ : i ≠ j), W.gr i) ≤ T j := iSup₂_le fun i hij => hT i j hij
    have hxT := hle hx'
    obtain ⟨g, hg, hgx⟩ := (hpart j x.1).mp ((hgr j x).mp hx)
    have h0 := hxT g hgx
    rw [hself j g hg, hgx] at h0
    exact Subtype.ext h0
  · rw [eq_top_iff]
    rintro ⟨a, ha⟩ -
    have hle : ∀ i, W.part i ≤ LinearMap.range W.A.val.toLinearMap := by
      intro i x hx
      exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩
    have hmap : Submodule.map W.A.val.toLinearMap (⨆ i, W.gr i) = ⨆ i, W.part i := by
      rw [Submodule.map_iSup]
      exact iSup_congr fun i => Submodule.map_comap_eq_self (hle i)
    have hmem : a ∈ Submodule.map W.A.val.toLinearMap (⨆ i, W.gr i) := by
      rw [hmap]
      exact ha
    obtain ⟨b, hb, hba⟩ := hmem
    have : b = ⟨a, ha⟩ := Subtype.ext hba
    rw [← this]
    exact hb
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_ext_approx {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (m : Ideal R)
    (A : Subalgebra O R) (T : Set R) (h0 : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ 2) (N : ℕ) (x : R) :
    ∃ a ∈ A, x - a ∈ m ^ N :=
  _root_.UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx m A T h0 hT hm N x

theorem UpperTheory.V.Alg.co_ext :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (R' : Type) [CommRing R'] [Algebra O R'] (I : Ideal R') [IsHausdorff I R'] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R → maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
      ∀ f f' : R →ₐ[O] R', (∃ n : ℕ, ∀ x ∈ maximalIdeal R ^ n, f x ∈ I ∧ f' x ∈ I) → f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f' := by
  intro O _ _ R _ _ _ B _ _ _ R' _ _ I _ i S hS hm f f' ⟨n, hn⟩ hi hs
  have hT : ∀ t ∈ S ∪ i '' (maximalIdeal B : Set B), t ∈ AlgHom.equalizer f f' ∧ t ∈ maximalIdeal R := by
    rintro t (ht | ⟨b, hb, rfl⟩)
    · exact ⟨hs t ht, hS ht⟩
    · refine ⟨DFunLike.congr_fun hi b, ?_⟩
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hb
  have hm' : maximalIdeal R ≤ Ideal.span (S ∪ i '' (maximalIdeal B : Set B)) ⊔ maximalIdeal R ^ 2 := by
    rw [Ideal.span_union]
    exact hm
  have key : ∀ g : R →ₐ[O] R', (∀ x ∈ maximalIdeal R ^ n, g x ∈ I) →
      ∀ k : ℕ, ∀ x ∈ maximalIdeal R ^ (n * k), g x ∈ I ^ k := by
    intro g hg k x hx
    rw [pow_mul] at hx
    have hle : (maximalIdeal R ^ n) ^ k ≤ (I ^ k).comap (g : R →+* R') :=
      le_trans (Ideal.pow_right_mono (fun y hy => hg y hy) k) (Ideal.le_comap_pow _ k)
    exact hle hx
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  obtain ⟨a, ha, h⟩ := co_ext_approx (maximalIdeal R) (AlgHom.equalizer f f') _
    (IsCO.res_surj (O := O)) hT hm' (n * k) x
  have ha' : f a = f' a := ha
  have : f x - f' x = f (x - a) - f' (x - a) := by rw [map_sub, map_sub, ha']; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, this]
  exact sub_mem (key f (fun y hy => (hn y hy).1) k _ h) (key f' (fun y hy => (hn y hy).2) k _ h)
end
