module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001

@[expose] public section

section

namespace ReciprocityTheory.AnForm.R

open IsLocalRing

variable {R : Type*} [CommRing R]

theorem exists_le_associated_of_dvd_prod_primes [IsDomain R] {ι : Type*} (f : ι → R) :
    ∀ (s : Multiset ι), (∀ i ∈ s, Prime (f i)) → ∀ {x : R}, x ∣ (s.map f).prod →
      ∃ t ≤ s, Associated x (t.map f).prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro _ x hx
    refine ⟨0, le_refl _, ?_⟩
    simp only [Multiset.map_zero, Multiset.prod_zero] at hx ⊢
    exact associated_one_iff_isUnit.2 (isUnit_of_dvd_one hx)
  | cons a s ih =>
    intro hs x hx
    have ha : Prime (f a) := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ i ∈ s, Prime (f i) := fun i hi => hs i (Multiset.mem_cons_of_mem hi)
    rw [Multiset.map_cons, Multiset.prod_cons] at hx
    by_cases hax : f a ∣ x
    · obtain ⟨y, rfl⟩ := hax
      have hy : y ∣ (s.map f).prod := (mul_dvd_mul_iff_left ha.ne_zero).1 hx
      obtain ⟨t, ht, hyt⟩ := ih hs' hy
      refine ⟨a ::ₘ t, Multiset.cons_le_cons a ht, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact hyt.mul_left (f a)
    · obtain ⟨z, hz⟩ := hx
      have h1 : f a ∣ x * z := ⟨(s.map f).prod, hz.symm⟩
      have h2 : f a ∣ z := (ha.dvd_or_dvd h1).resolve_left hax
      obtain ⟨w, rfl⟩ := h2
      have h3 : (s.map f).prod = x * w := by
        apply mul_left_cancel₀ ha.ne_zero
        rw [hz]
        ring
      obtain ⟨t, ht, hxt⟩ := ih hs' ⟨w, h3⟩
      exact ⟨t, ht.trans (Multiset.le_cons_self s a), hxt⟩

theorem prime_of_regular_params [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (i : Fin n) : Prime (f i) := by
  have hm : f i ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  exact prime_of_not_mem_sq hm ((regular_params_spec f hspan hdim).1 i)

theorem eq_unit_mul_monomial [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) {x : R} (hx0 : x ≠ 0) (hrad : (∏ i ∈ J, f i) ∈ (Ideal.span {x}).radical) :
    ∃ (u : Rˣ) (m : Fin n → ℕ), (∀ i, i ∉ J → m i = 0) ∧ x = u * ∏ i ∈ J, f i ^ m i := by
  obtain ⟨k, hk⟩ := hrad
  rw [Ideal.mem_span_singleton] at hk
  have hprimes : ∀ i ∈ k • J.val, Prime (f i) := fun i _ => prime_of_regular_params f hspan hdim i
  have hprod : ((k • J.val).map f).prod = (∏ i ∈ J, f i) ^ k := by
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
    rfl
  rw [← hprod] at hk
  obtain ⟨t, ht, hxt⟩ := exists_le_associated_of_dvd_prod_primes f (k • J.val) hprimes hk
  have htJ : ∀ i, i ∉ J → Multiset.count i t = 0 := fun i hi => Multiset.count_eq_zero.2 fun hit =>
    hi (Multiset.mem_of_mem_nsmul (Multiset.mem_of_le ht hit))
  obtain ⟨u, hu⟩ := hxt.symm
  refine ⟨u, fun i => Multiset.count i t, htJ, ?_⟩
  rw [← hu, Finset.prod_multiset_map_count, mul_comm]
  congr 1
  apply Finset.prod_subset
  · intro i hi
    by_contra hiJ
    exact Multiset.count_ne_zero.2 (Multiset.mem_toFinset.1 hi) (htJ i hiJ)
  · intro i _ hi
    rw [Multiset.count_eq_zero.2 (fun h => hi (Multiset.mem_toFinset.2 h)), pow_zero]

theorem ord_localization_eq_exponent [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] :
    Ring.ord (Localization.AtPrime (Ideal.span {f i}))
        (algebraMap R (Localization.AtPrime (Ideal.span {f i})) (u * ∏ j ∈ J, f j ^ m j)) =
      (m i : ℕ∞) := by
  have : IsDomain R := isDomain_of_isRegularLocalRing
  set P := Ideal.span {f i} with hP
  set S := Localization.AtPrime P
  have hpr : ∀ j, Prime (f j) := prime_of_regular_params f hspan hdim

  have hout : ∀ j, j ≠ i → f j ∉ P := by
    intro j hji hj
    rw [hP, Ideal.mem_span_singleton] at hj
    obtain ⟨c, hc⟩ := hj
    have hdc : f j ∣ f i * c := ⟨1, by rw [mul_one, hc]⟩
    rcases (hpr j).dvd_or_dvd hdc with h | h
    · exact (regular_params_spec f hspan hdim).2 j i hji
        (associated_of_dvd_dvd h ⟨c, hc⟩)
    · obtain ⟨d, rfl⟩ := h
      have : f j * 1 = f j * (f i * d) := by linear_combination hc
      have h1 := mul_left_cancel₀ (hpr j).ne_zero this
      exact (hpr i).not_isUnit (isUnit_of_dvd_one ⟨d, h1⟩)
  have hunit : ∀ j, j ≠ i → IsUnit (algebraMap R S (f j)) := fun j hj =>
    IsLocalization.map_units S (⟨f j, hout j hj⟩ : P.primeCompl)
  set π := algebraMap R S (f i)
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors P)
  have hπ0 : π ≠ 0 := fun h => (hpr i).ne_zero (hinj (by rw [map_zero]; exact h))
  have hπnzd : π ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hπ0
  have hmax : Ideal.span {π} = maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    show Ideal.span {π} = Ideal.map (algebraMap R S) (Ideal.span {f i})
    rw [Ideal.map_span, Set.image_singleton]
  have hord1 : Ring.ord S π = 1 := by
    unfold Ring.ord
    rw [hmax, Module.length_eq_one_iff]
    exact isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S))
  rw [← Finset.mul_prod_erase J _ hi, map_mul, map_mul, map_pow,
    Ring.ord_mul_of_isUnit_left ((Units.isUnit u).map _)]
  have hrest : IsUnit (algebraMap R S (∏ j ∈ J.erase i, f j ^ m j)) := by
    rw [map_prod]
    exact IsUnit.prod_iff.mpr fun j hj => by
      rw [map_pow]; exact (hunit j (Finset.ne_of_mem_erase hj)).pow _
  rw [Ring.ord_mul_of_isUnit_right hrest, Ring.ord_pow hπnzd, hord1, nsmul_eq_mul, mul_one]

end ReciprocityTheory.AnForm.R
end

section

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

theorem algebraMap_mem_nonZeroDivisors_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] {a : R} (ha : a ∈ nonZeroDivisors R) :
    algebraMap R S a ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right] at ha ⊢
  intro x hx
  obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  have h1 : algebraMap R S (y * a) = 0 := by
    rw [map_mul, ← IsLocalization.mk'_spec S y m, mul_right_comm, hx, zero_mul]
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff M S _).1 h1
  exact (IsLocalization.mk'_eq_zero_iff y m).2 ⟨c, ha _ (by rw [← hc, mul_assoc])⟩

theorem reesChart_lift {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} (g : Fin m → R)
    (j : Fin m) (hj : φ (g j) ∈ nonZeroDivisors S) (c : Fin m → S) (hc : ∀ k, φ (g k) = c k * φ (g j)) :
    ∃ ψ : FinalTheorems.reesChart g j →+* S, ψ.comp (algebraMap R (FinalTheorems.reesChart g j)) = φ := by
  let S' := Localization.Away (φ (g j))
  have hinj : Function.Injective (algebraMap S S') :=
    IsLocalization.injective S' (Submonoid.powers_le.2 hj)
  let L : Localization.Away (g j) →+* S' := IsLocalization.Away.map _ _ φ (g j)
  have hL : ∀ r, L (algebraMap R _ r) = algebraMap S S' (φ r) := fun r =>
    IsLocalization.map_eq _ _
  have key : ∀ x ∈ FinalTheorems.reesChart g j, L x ∈ (algebraMap S S').range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨c k, ?_⟩
      have hu : IsUnit (algebraMap S S' (φ (g j))) := IsLocalization.Away.algebraMap_isUnit _
      apply hu.mul_left_injective
      have := congrArg L (IsLocalization.mk'_spec (Localization.Away (g j)) (g k)
        (⟨g j, Submonoid.mem_powers _⟩ : Submonoid.powers (g j)))
      rw [map_mul, hL, hL] at this
      show algebraMap S S' (c k) * _ = L _ * _
      rw [← map_mul, ← hc]; exact this.symm
    | algebraMap r => exact ⟨φ r, (hL r).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let F : FinalTheorems.reesChart g j →+* (algebraMap S S').range :=
    (L.comp (FinalTheorems.reesChart g j).val.toRingHom).codRestrict _ (fun x => key x.1 x.2)
  let E : S ≃+* (algebraMap S S').range :=
    RingEquiv.ofBijective (algebraMap S S').rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap S S').rangeRestrict_surjective⟩
  refine ⟨E.symm.toRingHom.comp F, ?_⟩
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.symm_apply_eq]
  apply Subtype.ext
  simp [F, E, hL]
  try rfl

theorem ringEquiv_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {a : A}
    (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right] at ha ⊢
  intro x hx
  have : e.symm x * a = 0 := by
    apply e.injective; rw [map_mul, e.apply_symm_apply, hx, map_zero]
  simpa using congrArg e (ha _ this)

theorem effCartier_comap_of_isOpenImmersion' {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (hI : FinalTheorems.EffCartier I) : FinalTheorems.EffCartier (I.comap f) := by
  intro x
  obtain ⟨U, h, hxU, hh, hU⟩ := hI (f x)
  obtain ⟨r, hrle, hxr⟩ := U.2.exists_basicOpen_le (V := f.opensRange) ⟨f x, ⟨x, rfl⟩⟩ hxU
  have himg : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) = Y.basicOpen r := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 hrle]
  have hUX : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r) := by
    rw [← f.isAffineOpen_iff_of_isOpenImmersion, himg]; exact U.2.basicOpen r
  have hle : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) ≤ U.1 := himg.le.trans (Y.basicOpen_le r)
  have hnzd : ∀ (O : Y.Opens) (hO : O = Y.basicOpen r) (hOU : O ≤ U.1),
      Y.presheaf.map (homOfLE hOU).op h ∈ nonZeroDivisors Γ(Y, O) := by
    rintro O rfl hOU
    have := U.2.isLocalization_basicOpen r
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers r) hh
  let e := (f.appIso (f ⁻¹ᵁ Y.basicOpen r)).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hUX⟩, e (Y.presheaf.map (homOfLE hle).op h), hxr, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors e (hnzd _ himg hle)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    rw [← I.map_ideal (U := ⟨_, (f.isAffineOpen_iff_of_isOpenImmersion).2 hUX⟩) (V := U) hle, hU,
      Ideal.map_span, Set.image_singleton]
    rw [show ((f.appIso (f ⁻¹ᵁ Y.basicOpen r)).inv.hom : _ →+* _) = (e.symm : _ →+* _) from rfl,
      Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
    rfl

theorem inter_reesCharts' {X W : Scheme.{0}} (π : W ⟶ X) (J : X.IdealSheafData) (hB : FinalTheorems.Blowup π J)
    (U : X.affineOpens) {m : ℕ} (g : Fin m → Γ(X, U.1)) (_hg : Ideal.span (Set.range g) = J.ideal U)
    (V : Fin m → W.Opens) (hV : ∀ i, V i ≤ π ⁻¹ᵁ U.1)
    (e : ∀ i, (V i).toScheme ≅ Spec (CommRingCat.of (FinalTheorems.reesChart g i)))
    (he : ∀ i, (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (FinalTheorems.reesChart g i))) ≫
      U.2.fromSpec = (V i).ι ≫ π)
    (i j : Fin m) (t : Γ(W, V i))
    (ht : t = (V i).topIso.hom ((e i).hom.appTop ((Scheme.ΓSpecIso _).inv
      ⟨IsLocalization.mk' (Localization.Away (g i)) (g j) (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)),
        Algebra.subset_adjoin ⟨j, rfl⟩⟩))) :
    V i ⊓ V j = W.basicOpen t := by
  classical
  let σ : ∀ k, FinalTheorems.reesChart g k →+* Γ(W, V k) := fun k =>
    (V k).topIso.hom.hom.comp (((e k).hom.appTop).hom.comp
      (Scheme.ΓSpecIso (.of (FinalTheorems.reesChart g k))).inv.hom)
  let q : ∀ k l, FinalTheorems.reesChart g k := fun k l =>
    ⟨IsLocalization.mk' (Localization.Away (g k)) (g l) (⟨g k, Submonoid.mem_powers _⟩ : Submonoid.powers (g k)),
      Algebra.subset_adjoin ⟨l, rfl⟩⟩
  have hq : ∀ k l, algebraMap Γ(X, U.1) (FinalTheorems.reesChart g k) (g l) =
      q k l * algebraMap Γ(X, U.1) (FinalTheorems.reesChart g k) (g k) := fun k l =>
    Subtype.ext (IsLocalization.mk'_spec _ _ _).symm
  have hsec : ∀ k r, σ k (algebraMap _ _ r) = π.appLE _ (V k) (hV k) r := fun k r =>
    sec_algebraMap_of_iso π U (V k) (hV k) _ (e k) (he k) r
  have hP : ∀ k l, π.appLE _ (V k) (hV k) (g l) = σ k (q k l) * π.appLE _ (V k) (hV k) (g k) := by
    intro k l; rw [← hsec, ← hsec, ← map_mul, ← hq]
  have hnz : ∀ k, π.appLE _ (V k) (hV k) (g k) ∈ nonZeroDivisors Γ(W, V k) := by
    intro k
    rw [← hsec]
    apply sec_mem_nonZeroDivisors (V k) (e k)
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hu : IsUnit (algebraMap Γ(X, U.1) (Localization.Away (g k)) (g k)) :=
      IsLocalization.Away.algebraMap_isUnit _
    apply Subtype.ext
    exact hu.mul_left_eq_zero.1 (congrArg Subtype.val hx)
  have hti : t = σ i (q i j) := ht
  have hVi : IsAffineOpen (V i) := isAffineOpen_of_iso (V i) (e i)
  apply le_antisymm
  · intro w hw
    have hwi : w ∈ V i := hw.1
    have hwj : w ∈ V j := hw.2
    rw [Scheme.mem_basicOpen W t w hwi, hti]
    have hg : ∀ k l (hwk : w ∈ V k), W.presheaf.germ (V k) w hwk (π.appLE _ (V k) (hV k) (g l)) =
        W.presheaf.germ (π ⁻¹ᵁ U.1) w (hV k hwk) (π.app U.1 (g l)) := by
      intro k l hwk
      simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
    have h1 := congrArg (W.presheaf.germ (V i) w hwi) (hP i j)
    have h2 := congrArg (W.presheaf.germ (V j) w hwj) (hP j i)
    rw [map_mul, hg, hg] at h1
    rw [map_mul, hg, hg] at h2
    have hA := germ_mem_nonZeroDivisors hVi (hnz i) w hwi
    rw [hg] at hA
    have h3 : (W.presheaf.germ (V j) w hwj (σ j (q j i)) * W.presheaf.germ (V i) w hwi (σ i (q i j)) - 1) *
        W.presheaf.germ (π ⁻¹ᵁ U.1) w (hV i hwi) (π.app U.1 (g i)) = 0 := by
      rw [sub_mul, one_mul, mul_assoc, ← h1, ← h2, sub_self]
    have h4 := sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hA) _ h3)
    exact IsUnit.of_mul_eq_one_right _ h4
  · have hD : IsAffineOpen (W.basicOpen t) := hVi.basicOpen t
    have hDle : W.basicOpen t ≤ V i := W.basicOpen_le t
    have hDU : W.basicOpen t ≤ π ⁻¹ᵁ U.1 := hDle.trans (hV i)
    let ρ := W.presheaf.map (homOfLE hDle).op
    let φ := π.appLE U.1 (W.basicOpen t) hDU
    have hφ : ∀ l, φ (g l) = ρ (π.appLE _ (V i) (hV i) (g l)) := fun l => by
      show _ = (π.appLE _ (V i) (hV i) ≫ W.presheaf.map (homOfLE hDle).op) (g l)
      rw [Scheme.Hom.appLE_map]
    have hu : IsUnit (ρ t) := W.toRingedSpace.isUnit_res_basicOpen t
    have key : ∀ (a b u x : Γ(W, W.basicOpen t)), u * x = 1 → a * b = a * u * (x * b) := by
      intro a b u x h; linear_combination (-(a * b)) * h
    have hc : ∀ l, φ.hom (g l) = (ρ (σ i (q i l)) * ↑hu.unit⁻¹) * φ.hom (g j) := by
      intro l
      show φ (g l) = _ * φ (g j)
      rw [hφ, hφ, hP i l, hP i j, ← hti, map_mul, map_mul]
      exact key _ _ _ _ hu.val_inv_mul
    have hnzj : φ.hom (g j) ∈ nonZeroDivisors Γ(W, W.basicOpen t) := by
      show φ (g j) ∈ _
      rw [hφ, hP i j, map_mul, ← hti]
      exact mul_mem hu.mem_nonZeroDivisors (res_mem_nonZeroDivisors hDle hVi (hnz i))
    obtain ⟨ψ, hψ⟩ := reesChart_lift φ.hom g j hnzj _ hc
    let a := hD.fromSpec
    let b := Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv ≫ (V j).ι
    have hab : b ≫ π = a ≫ π := by
      simp only [a, b, Category.assoc]
      rw [← he j, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ,
        ← IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hD hDU]
      rfl
    have hE : FinalTheorems.EffCartier (J.comap (a ≫ π)) := by
      rw [Scheme.IdealSheafData.comap_comp]; exact effCartier_comap_of_isOpenImmersion' _ a hB.1
    obtain ⟨h0, -, huniq⟩ := hB.2 _ (a ≫ π) hE
    have hab' : b = a := (huniq b hab).trans (huniq a rfl).symm
    intro w hw
    have hw' : w ∈ Set.range hD.fromSpec := by rw [hD.range_fromSpec]; exact hw
    obtain ⟨x, rfl⟩ := hw'
    refine ⟨hDle hw, ?_⟩
    change a x ∈ V j
    rw [← hab']
    change (V j).ι ((Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv) x) ∈ V j
    exact ((Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv) x).2

end

end ReciprocityTheory.AnForm.R
end
