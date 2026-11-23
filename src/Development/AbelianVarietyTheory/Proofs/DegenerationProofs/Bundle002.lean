module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.FieldTheory.Normal.Basic

@[expose] public section

section

open Module TensorProduct

namespace GlobalTheory.ZModPerp

theorem exists_eq_nsmul_zmod {n r N : ℕ} [NeZero n] (h : r * N = n) (y : ZMod n)
    (hy : N • y = 0) : ∃ z : ZMod n, y = r • z := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using h.symm)
  have h1 : ((N * y.val : ℕ) : ZMod n) = 0 := by
    simpa [nsmul_eq_mul] using hy
  rw [ZMod.natCast_eq_zero_iff] at h1
  replace h1 : N * r ∣ N * y.val := by rwa [mul_comm N r, h]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hN) h1
  refine ⟨(k : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val y, hk]
  simp [nsmul_eq_mul]

theorem dvd_of_forall_mul_eq_zero {n : ℕ} [NeZero n] (x y : ZMod n)
    (h : ∀ a : ZMod n, a * x = 0 → a * y = 0) : x ∣ y := by
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right x.val n
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left x.val n
  have h1 : (m : ZMod n) * x = 0 := by
    have : ((m * x.val : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      refine ⟨k, ?_⟩
      calc m * x.val = m * (Nat.gcd x.val n * k) := by rw [← hk]
        _ = (Nat.gcd x.val n * m) * k := by ring
        _ = n * k := by rw [← hm]
    simpa using this
  obtain ⟨z, hz⟩ := exists_eq_nsmul_zmod hm.symm y (by simpa [nsmul_eq_mul] using h _ h1)
  have h2 := congrArg (Int.cast : ℤ → ZMod n) (Nat.gcd_eq_gcd_ab x.val n)
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    ZMod.natCast_zmod_val] at h2
  rw [hz, nsmul_eq_mul, h2, mul_assoc]
  exact dvd_mul_right _ _

theorem isPrincipalIdealRing_zmod (n : ℕ) : IsPrincipalIdealRing (ZMod n) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) (ZMod.ringHom_surjective _)

theorem baer_zmod (n : ℕ) [NeZero n] : Module.Baer (ZMod n) (ZMod n) := by
  intro I g
  obtain ⟨x, rfl⟩ := ((isPrincipalIdealRing_zmod n).principal I).principal
  have hx : x ∈ Submodule.span (ZMod n) {x} := Submodule.mem_span_singleton_self x
  obtain ⟨c, hc⟩ := dvd_of_forall_mul_eq_zero x (g ⟨x, hx⟩) fun a ha => by
    rw [← smul_eq_mul, ← map_smul]
    have : a • (⟨x, hx⟩ : Submodule.span (ZMod n) {x}) = 0 := Subtype.ext ha
    rw [this, map_zero]
  refine ⟨LinearMap.toSpanSingleton _ _ c, fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have : (⟨a • x, hy⟩ : Submodule.span (ZMod n) {x}) = a • ⟨x, hx⟩ := rfl
  rw [this, map_smul g, hc]
  simp [mul_assoc]

theorem exists_dual_ne_zero {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    {q : M} (hq : q ≠ 0) : ∃ f : Dual (ZMod n) M, f q ≠ 0 := by
  obtain ⟨x, hx⟩ := ((isPrincipalIdealRing_zmod n).principal
    (LinearMap.ker (LinearMap.toSpanSingleton (ZMod n) M q))).principal
  have hx' : ∀ a : ZMod n, a • q = 0 ↔ x ∣ a := fun a => by
    rw [← Ideal.mem_span_singleton, ← Ideal.submodule_span_eq, ← hx]
    simp
  obtain ⟨c, hc, hc0⟩ : ∃ c : ZMod n, c * x = 0 ∧ c ≠ 0 := by
    by_contra! H
    have := dvd_of_forall_mul_eq_zero x 1 fun a ha => by simp [H a ha]
    exact hq (by simpa using (hx' 1).mpr this)
  have H : ∀ a : ZMod n, a • q = 0 → (RingHom.id (ZMod n)) a • c = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := (hx' a).mp ha
    simp only [RingHom.id_apply, smul_eq_mul]
    linear_combination b * hc
  let φ := LinearPMap.mkSpanSingleton' q c H
  obtain ⟨f, hf⟩ := (baer_zmod n).extension_property φ.domain.subtype
    φ.domain.subtype_injective φ.toFun
  refine ⟨f, ?_⟩
  have := LinearMap.congr_fun hf ⟨q, Submodule.mem_span_singleton_self q⟩
  have h2 := LinearPMap.mkSpanSingleton'_apply_self q c H (Submodule.mem_span_singleton_self q)
  have h3 : f q = c := this.trans h2
  rwa [h3]

theorem baer_of_free {n : ℕ} [NeZero n] (M : Type*) [AddCommGroup M] [Module (ZMod n) M]
    [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M] : Module.Baer (ZMod n) M := by
  let b := Module.Free.chooseBasis (ZMod n) M
  refine Module.Baer.of_equiv b.equivFun.symm fun I g => ?_
  choose l hl using fun i => baer_zmod n I ((LinearMap.proj i).comp g)
  exact ⟨LinearMap.pi l, fun x hx => funext fun i => hl i x hx⟩

theorem exists_eq_nsmul_of_free {n r N : ℕ} [NeZero n] (h : r * N = n) {M : Type*}
    [AddCommGroup M] [Module (ZMod n) M] [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M]
    (y : M) (hy : N • y = 0) : ∃ z : M, y = r • z := by
  let b := Module.Free.chooseBasis (ZMod n) M
  choose z hz using fun i => exists_eq_nsmul_zmod h (b.equivFun y i) (by
    rw [← Pi.smul_apply, ← map_nsmul, hy, map_zero, Pi.zero_apply])
  refine ⟨b.equivFun.symm z, b.equivFun.injective ?_⟩
  rw [map_nsmul, LinearEquiv.apply_symm_apply]
  exact funext hz

theorem free_of_isCompl {R M : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] {T T' : Submodule R M} [Module.Free R T]
    (h : IsCompl T T') : Module.Free R T' := by
  let e := Submodule.prodEquivOfIsCompl T T' h
  have : Module.Finite R T := Module.Finite.of_surjective (T.projectionOnto T' h)
    (Submodule.projectionOnto_surjective h)
  have : Module.Finite R T' := Module.Finite.of_surjective (T'.projectionOnto T h.symm)
    (Submodule.projectionOnto_surjective h.symm)
  have : Module.Projective R T' :=
    Module.Projective.of_split T'.subtype (T'.projectionOnto T h.symm) (by ext; simp)
  refine Module.free_of_flat_of_finrank_eq R T' (finrank R M - finrank R T) fun P => ?_
  let := P.isMaximal
  let := Ideal.Quotient.field P.asIdeal
  have : Nontrivial R := (Ideal.Quotient.mk P.asIdeal).domain_nontrivial
  have e' : ((R ⧸ P.1) ⊗[R] M) ≃ₗ[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] T) × ((R ⧸ P.1) ⊗[R] T') :=
    (e.symm.baseChange R (R ⧸ P.1) _ _).trans (TensorProduct.prodRight R (R ⧸ P.1) _ _ _)
  have := e'.finrank_eq
  rw [finrank_prod, finrank_baseChange, finrank_baseChange] at this
  omega

end GlobalTheory.ZModPerp

namespace GlobalTheory

open ZModPerp

theorem orthogonal_free_of_perfect_alt_zmod :
    ∀ (N r : ℕ) [NeZero (r * N)] (Γ : Type) [AddCommGroup Γ] [Module (ZMod (r * N)) Γ]
      [Module.Free (ZMod (r * N)) Γ] [Module.Finite (ZMod (r * N)) Γ]
      (e : LinearMap.BilinForm (ZMod (r * N)) Γ), e.IsAlt → Function.Bijective e →
      (∀ H : Submodule (ZMod (r * N)) Γ, e.orthogonal (e.orthogonal H) = H) ∧
      ∀ T : Submodule (ZMod (r * N)) Γ, Module.Free (ZMod (r * N)) T →
        (∃ T', IsCompl T T') ∧ Module.Free (ZMod (r * N)) (e.orthogonal T) ∧
        (∀ t ∈ T, N • t = 0 ↔ ∃ t' ∈ T, t = r • t') ∧
        ∀ a : Γ, (∀ t ∈ T, r • e a t = 0) ↔ ∃ h ∈ e.orthogonal T, r • a = r • h := by
  intro N r _ Γ _ _ _ _ e halt hbij
  have hmem : ∀ (H : Submodule (ZMod (r * N)) Γ) (x : Γ),
      x ∈ e.orthogonal H ↔ ∀ y ∈ H, e x y = 0 := fun H x => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact forall₂_congr fun y _ => ⟨halt.isRefl _ _, halt.isRefl _ _⟩
  have hkill : ∀ x : Γ, (r * N) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (r * N)), ZMod.natCast_self, zero_smul]
  refine ⟨fun H => le_antisymm (fun x hx => ?_) (fun x hx => ?_), fun T hT => ?_⟩
  · by_contra hxH
    obtain ⟨f, hf⟩ := exists_dual_ne_zero (n := r * N) (q := H.mkQ x)
      (by simpa using hxH)
    obtain ⟨b, hb⟩ := hbij.2 (f ∘ₗ H.mkQ)
    have hb' : b ∈ e.orthogonal H := (hmem _ _).mpr fun y hy => by
      rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero H).mpr hy,
        map_zero]
    have := halt.isRefl _ _ ((hmem _ _).mp hx b hb')
    rw [hb] at this
    exact hf this
  · exact (hmem _ _).mpr fun y hy => halt.isRefl _ _ ((hmem _ _).mp hy x hx)
  · obtain ⟨p, hp⟩ := (baer_of_free (n := r * N) T).extension_property T.subtype
      T.subtype_injective LinearMap.id
    have hp' : ∀ t : T, p t = t := fun t => LinearMap.congr_fun hp t
    have hc : IsCompl T (LinearMap.ker p) := LinearMap.isCompl_of_proj hp'
    refine ⟨⟨_, hc⟩, ?_, fun t ht => ⟨fun h => ?_, ?_⟩, fun a => ⟨fun h => ?_, ?_⟩⟩
    · have := free_of_isCompl hc
      have : Module.Free (ZMod (r * N)) (Γ ⧸ T) :=
        Module.Free.of_equiv (Submodule.quotientEquivOfIsCompl T _ hc).symm
      have E : e.orthogonal T ≃ₗ[ZMod (r * N)] T.dualAnnihilator :=
        (LinearEquiv.ofBijective e hbij).ofSubmodules _ _ (by
          ext f
          obtain ⟨b, rfl⟩ := hbij.2 f
          simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator, hmem]
          constructor
          · rintro ⟨x, hx, hxb⟩
            rw [← hxb]
            exact hx
          · exact fun h => ⟨b, h, rfl⟩)
      exact Module.Free.of_equiv (E.trans T.dualQuotEquivDualAnnihilator.symm).symm
    · obtain ⟨z, hz⟩ := exists_eq_nsmul_of_free (n := r * N) rfl (⟨t, ht⟩ : T) (Subtype.ext h)
      exact ⟨z, z.2, congrArg Subtype.val hz⟩
    · rintro ⟨t', -, rfl⟩
      rw [← mul_smul, mul_comm, hkill]
    · obtain ⟨l, hl⟩ := exists_eq_nsmul_of_free (n := r * N) (mul_comm N r)
        (M := Dual (ZMod (r * N)) T) (e a ∘ₗ T.subtype) (LinearMap.ext fun t => h t t.2)
      obtain ⟨b, hb⟩ := hbij.2 (l ∘ₗ p)
      refine ⟨a - N • b, (hmem _ _).mpr fun y hy => ?_, ?_⟩
      · have h1 : e a y = N • l ⟨y, hy⟩ := LinearMap.congr_fun hl ⟨y, hy⟩
        have h2 : e b y = l ⟨y, hy⟩ := by
          rw [hb, LinearMap.comp_apply, hp' ⟨y, hy⟩]
        rw [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, sub_self]
      · rw [smul_sub, ← mul_smul, hkill, sub_zero]
    · rintro ⟨h, hh, hah⟩ t ht
      rw [← LinearMap.smul_apply, ← map_nsmul, hah, map_nsmul, LinearMap.smul_apply,
        (hmem _ _).mp hh t ht, smul_zero]

end GlobalTheory
end

section

open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem exists_forall_ne_zero_of_countable_analytic :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (U : Set E),
      IsOpen U → IsPreconnected U → U.Nonempty → ∀ (ι : Type) [Countable ι] (f : ι → E → ℂ),
      (∀ i, AnalyticOnNhd ℂ (f i) U) → (∀ i, ∃ x ∈ U, f i x ≠ 0) →
      ∃ x ∈ U, ∀ i, f i x ≠ 0 := by
  intro E _ _ _ U hU hc hne ι _ f hf hnz
  let S : ι → Set E := fun i => (U ∩ f i ⁻¹' ({0}ᶜ)) ∪ (closure U)ᶜ
  have hopen : ∀ i, IsOpen (S i) := fun i =>
    ((hf i).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hdense : ∀ i, Dense (S i) := by
    intro i
    rw [dense_iff_inter_open]
    intro V hV hVne
    by_cases hVU : (V ∩ U).Nonempty
    · obtain ⟨z, hzV, hzU⟩ := hVU
      by_contra hcon
      have hzero : ∀ y ∈ V ∩ U, f i y = 0 := by
        intro y hy
        by_contra hy0
        exact hcon ⟨y, hy.1, Or.inl ⟨hy.2, hy0⟩⟩
      have hev : f i =ᶠ[nhds z] 0 := by
        filter_upwards [(hV.inter hU).mem_nhds ⟨hzV, hzU⟩] with y hy
        exact hzero y hy
      have hall := (hf i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU hev
      obtain ⟨x, hxU, hx⟩ := hnz i
      exact hx (hall hxU)
    · obtain ⟨z, hzV⟩ := hVne
      refine ⟨z, hzV, Or.inr ?_⟩
      intro hz
      exact hVU (mem_closure_iff.1 hz V hV hzV)
  have hD : Dense (⋂ i, S i) := dense_iInter_of_isOpen hopen hdense
  obtain ⟨x, hxU, hx⟩ := hD.inter_open_nonempty U hU hne
  refine ⟨x, hxU, fun i => ?_⟩
  rcases Set.mem_iInter.1 hx i with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h

end GlobalTheory
end

section

open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem coeff_eq_zero_of_hasSum_mFourier_orthonormal_image {J : Type} [Fintype J] {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : C(UnitAddTorus J, ℂ) →L[ℂ] E)
    (hL : Orthonormal ℂ (fun n : J → ℤ => L (UnitAddTorus.mFourier n))) (b : (J → ℤ) → ℂ)
    (h : HasSum (fun s => b s • UnitAddTorus.mFourier s) (0 : C(UnitAddTorus J, ℂ)))
    (t : J → ℤ) : b t = 0 := by
  classical
  have h1 := ((innerSL ℂ (L (UnitAddTorus.mFourier t))).comp L).hasSum h
  have h2 : HasSum (fun s => if s = t then b t else 0) (0 : ℂ) := by
    rw [map_zero] at h1
    refine HasSum.congr_fun h1 fun s => ?_
    have := orthonormal_iff_ite.mp hL t s
    simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, this, smul_eq_mul]
    by_cases hs : s = t
    · simp [hs]
    · simp [hs, Ne.symm hs]
  exact (hasSum_ite_eq t (b t)).unique h2

theorem mFourier_coe_eq_exp {J : Type} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    UnitAddTorus.mFourier s (fun j => (x j : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

theorem coeff_eq_zero_of_fourier_series_eq_zero :
    ∀ (J : Type) [Fintype J] (b : (J → ℤ) → ℂ), (Summable fun s => ‖b s‖) →
      (∀ x : J → ℝ, ∑' s, b s *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) = 0) →
      ∀ s, b s = 0 := by
  intro J _ b hb h0 t
  have hs : Summable (fun s => b s • UnitAddTorus.mFourier s : (J → ℤ) → C(UnitAddTorus J, ℂ)) := by
    refine Summable.of_norm ?_
    simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using hb
  have hz : (∑' s, b s • UnitAddTorus.mFourier s : C(UnitAddTorus J, ℂ)) = 0 := by
    ext y
    choose x hx using fun j => QuotientAddGroup.mk_surjective (y j)
    have hy : y = fun j => (x j : UnitAddCircle) := funext fun j => (hx j).symm
    have h1 := ((ContinuousMap.evalCLM ℂ y).hasSum hs.hasSum).tsum_eq
    simp only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] at h1
    rw [← h1, hy]
    simp only [mFourier_coe_eq_exp]
    simpa using h0 x
  have hsum := hs.hasSum
  rw [hz] at hsum
  exact coeff_eq_zero_of_hasSum_mFourier_orthonormal_image _ UnitAddTorus.orthonormal_mFourier b hsum t

end GlobalTheory
end

section

open Module

namespace GlobalTheory

theorem hasSum_map_powerSeries_mk_finsum : ∀ (O K Z : Type) [CommRing O] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (φ : PowerSeries O →+* K), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (deg : Z → ℕ), (∀ n, {z | deg z = n}.Finite) → ∀ a : Z → O, HasSum (fun z => φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) (φ (PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z)) := by
  intro O K Z _ _ _ _ φ h1 hX deg hfin a
  classical
  set F : PowerSeries O := PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z with hF
  have key : ∀ (n : ℕ) (s : Finset Z), (∀ z, deg z < n → z ∈ s) →
      ‖(∑ z ∈ s, φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) - φ F‖
        ≤ ‖φ PowerSeries.X‖ ^ n := by
    intro n s hs
    have hdvd : (PowerSeries.X : PowerSeries O) ^ n ∣
        (∑ z ∈ s, PowerSeries.C (a z) * PowerSeries.X ^ deg z) - F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm

      rw [map_sub, map_sum, hF, PowerSeries.coeff_mk, sub_eq_zero]
      have : (∑ᶠ (z : Z) (_ : deg z = m), a z) = ∑ z ∈ s.filter (fun z => deg z = m), a z := by
        rw [← finsum_mem_coe_finset]
        refine finsum_congr fun z => ?_
        refine finsum_congr_Prop ?_ (fun _ => rfl)
        apply propext
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨fun h => ⟨hs z (h ▸ hm), h⟩, fun h => h.2⟩
      rw [this, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases h : deg z = m
      · simp [h]
      · simp [h, Ne.symm h]
    obtain ⟨g, hg⟩ := hdvd
    have h2 := congrArg φ hg

    simp only [map_sub, map_sum, map_mul, map_pow] at h2
    rw [h2, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (h1 g)
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hX
  have hfn : {z | deg z < n}.Finite := by
    refine ((Set.finite_Iio n).biUnion (fun m _ => hfin m)).subset ?_
    intro z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iio]
    exact ⟨deg z, hz, rfl⟩
  simp only [SummationFilter.unconditional_filter]
  filter_upwards [Filter.eventually_ge_atTop hfn.toFinset] with s hs
  rw [dist_eq_norm]
  exact (key n s fun z hz => hs (hfn.mem_toFinset.2 hz)).trans_lt hn

end GlobalTheory
end

section

namespace GlobalTheory

open IntermediateField Polynomial

theorem compositum_finite_normal_isPGroup (K K' Ω : Type) [Field K] [Field K'] [Field Ω]
    [Algebra K K'] [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] (l : ℕ)
    (L : IntermediateField K Ω) (hfin : FiniteDimensional K L) (hn : Normal K L)
    (hp : IsPGroup l (L ≃ₐ[K] L)) :
    FiniteDimensional K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      Normal K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      IsPGroup l (IntermediateField.adjoin K' (L : Set Ω) ≃ₐ[K']
        IntermediateField.adjoin K' (L : Set Ω)) := by
  obtain ⟨p, hsp⟩ := Normal.exists_isSplittingField K L
  obtain ⟨hs, hL⟩ := IntermediateField.isSplittingField_iff.mp hsp
  have hsΩ : (p.map (algebraMap K Ω)).Splits := by
    have := hs.map (algebraMap L Ω)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  have hmm : (p.map (algebraMap K K')).map (algebraMap K' Ω) = p.map (algebraMap K Ω) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hroot : (p.map (algebraMap K K')).rootSet Ω = p.rootSet Ω := by
    simp only [Polynomial.rootSet, Polynomial.aroots, hmm]
  have hE : IntermediateField.adjoin K' (L : Set Ω) =
      IntermediateField.adjoin K' ((p.map (algebraMap K K')).rootSet Ω) := by
    rw [hroot]
    conv_lhs => rw [hL]
    exact IntermediateField.adjoin_adjoin_right _ _
  have hsp' : (p.map (algebraMap K K')).IsSplittingField K'
      (IntermediateField.adjoin K' (L : Set Ω)) := by
    rw [hE]
    exact IntermediateField.adjoin_rootSet_isSplittingField (by rw [hmm]; exact hsΩ)
  refine ⟨Polynomial.IsSplittingField.finiteDimensional _ (p.map (algebraMap K K')),
    Normal.of_isSplittingField (p.map (algebraMap K K')), ?_⟩
  set E := IntermediateField.adjoin K' (L : Set Ω) with hEdef
  let i : L →ₐ[K] E :=
    { toFun := fun x => ⟨x, IntermediateField.subset_adjoin K' _ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  letI : Algebra L E := i.toRingHom.toAlgebra
  haveI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  let r : (E ≃ₐ[K'] E) →* (E ≃ₐ[K] E) :=
    { toFun := fun g => g.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let φ : (E ≃ₐ[K'] E) →* (L ≃ₐ[K] L) := (AlgEquiv.restrictNormalHom L).comp r
  refine hp.of_injective φ ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ x : L, g (i x) = i x := by
    intro x
    have h1 := AlgEquiv.restrictNormal_commutes (r g) L x
    have h2 : (r g).restrictNormal L = 1 := hg
    rw [h2] at h1
    exact h1.symm
  have : (g : E →ₐ[K'] E) = AlgHom.id K' E :=
    IntermediateField.adjoin_algHom_ext K' fun x hx => hfix ⟨x, hx⟩
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun this x)

end GlobalTheory
end
