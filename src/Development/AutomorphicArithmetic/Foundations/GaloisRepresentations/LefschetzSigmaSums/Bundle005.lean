module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.LocalSmoothExtension

private def Tw (_σ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance twAdd (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : AddCommGroup (Tw σ V) :=
  inferInstanceAs (AddCommGroup V)

private instance twMod (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Tw σ V) :=
  Module.compHom V (σ.symm : ℂ →+* ℂ)

private def toTw (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : V ≃+ Tw σ V := AddEquiv.refl V

private theorem tw_smul (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (c : ℂ) (x : V) :
    toTw σ V (c • x) = σ c • toTw σ V x := by
  change c • x = ((σ.symm : ℂ →+* ℂ) (σ c)) • x
  simp

private theorem tw_smul' (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (c : ℂ) (x : Tw σ V) :
    c • x = toTw σ V (σ.symm c • (toTw σ V).symm x) := rfl

private theorem tw_finite (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] : FiniteDimensional ℂ (Tw σ V) := by
  let b := Module.finBasis ℂ V
  have hsm : ∀ (c : ℂ) (y : Tw σ V), (toTw σ V).symm (c • y) = σ.symm c • (toTw σ V).symm y :=
    fun c y => rfl
  let b' : Module.Basis (Fin (Module.finrank ℂ V)) ℂ (Tw σ V) := Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr ((toTw σ V).symm y))
      invFun := fun f => toTw σ V (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        simp [hsm]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr ((toTw σ V).symm y))) =
              b.repr ((toTw σ V).symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }
  exact Module.Finite.of_basis b'

private def twMap (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] V) :
    Tw σ V →ₗ[ℂ] Tw σ V where
  toFun x := toTw σ V (T ((toTw σ V).symm x))
  map_add' x y := by simp
  map_smul' c x := by
    rw [RingHom.id_apply, tw_smul', tw_smul']
    simp

theorem conjRep_of : ConjRep := by
  intro σ Γ V _ _ _ _ ξ
  let ξ' : Representation ℂ Γ (Tw σ V) :=
    { toFun := fun g => twMap σ V (ξ g)
      map_one' := by
        ext x
        simp [twMap]
      map_mul' := fun g h => by
        ext x
        simp [twMap, Module.End.mul_apply] }
  exact ⟨Tw σ V, twAdd σ V, twMod σ V, tw_finite σ V, ξ', toTw σ V, tw_smul σ V, fun g x => rfl⟩

end UpperTheory.Gal.LocalSmoothExtension
end
end

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cxLin_of :
    CxFlat → CxLin := by
  intro hflat p _ G v K m f a hfin A w c
  classical
  have hU : (⋃ i, {z : Σ q : GlobalTheory.LKCx.FCls G, PtsOf G v K q × GlobalTheory.LKCx.grp G (Quot.out q).β |
      Seen G v K (f i) z.1 z.2.1 z.2.2}).Finite := Set.finite_iUnion hfin
  have hS : ∀ i z, Seen G v K (f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro i z hz
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.2 ⟨i, hz⟩
  have hS' : ∀ z, Seen G v K (∑ i, a i • f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Finset.sum_apply] at h2
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    refine hS i z ⟨h1, ?_, h3⟩
    intro h0
    apply hi
    simp [Pi.smul_apply, smul_eq_mul, h0]
  have hR : ∀ α i, GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) =
      ∑ z ∈ hU.toFinset, summ G v (c α) K (f i) z :=
    fun α i => hflat p G v (c α) K (f i) hU.toFinset (hS i)
  have hT : ∀ z, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z =
      ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := by
    intro z
    unfold summ
    split_ifs with hfix
    · simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      ring
    · simp [Finsupp.sum]
  calc GlobalTheory.RootSumWeights.cxTotalM G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) (Kp G) (oneP G)
      = ∑ z ∈ hU.toFinset, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z :=
        hflat p G v _ K _ hU.toFinset hS'
    _ = ∑ z ∈ hU.toFinset, ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z :=
        Finset.sum_congr rfl fun z _ => hT z
    _ = ∑ i, ∑ z ∈ hU.toFinset, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := Finset.sum_comm
    _ = ∑ i, a i * w.sum fun α r => r * GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finsupp.sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hR α i, Finset.mul_sum]
end

section

set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem invPolProps_of (hR : InvRoots) : InvPolProps := by
  intro F _ _ P hP
  have hP0 : P ≠ 0 := fun h => hP (by simp [h])
  have hc : (P.coeff 0)⁻¹ ≠ 0 := inv_ne_zero hP
  have hrr : ∀ Q : F[X], Q.coeff 0 ≠ 0 → Q.reverse.reverse = Q := by
    intro Q hQ
    have hQd : Q.reverse.natDegree = Q.natDegree := by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hQ), Nat.sub_zero]
    ext n
    rw [coeff_reverse, hQd, coeff_reverse, revAt_invol]
  have hdeg : P.reverse.natDegree = P.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold invPol
    rw [natDegree_C_mul hc, hdeg]
  · unfold invPol
    rw [mul_coeff_zero, coeff_C_zero, coeff_zero_reverse]
    exact mul_ne_zero hc (leadingCoeff_ne_zero.mpr hP0)
  · intro hs
    unfold invPol
    have hrs : P.reverse.Separable := by
      rw [PerfectField.separable_iff_squarefree]
      intro x hx
      obtain ⟨y, hy⟩ := hx
      have hx0 : x.coeff 0 ≠ 0 := by
        intro h0
        have h1 : P.reverse.coeff 0 = 0 := by
          rw [hy, mul_coeff_zero, mul_coeff_zero, h0, zero_mul, zero_mul]
        rw [coeff_zero_reverse] at h1
        exact leadingCoeff_ne_zero.mpr hP0 h1
      have hPx : x.reverse * x.reverse ∣ P := by
        refine ⟨y.reverse, ?_⟩
        rw [← hrr P hP, hy, reverse_mul_of_domain, reverse_mul_of_domain]
      have hu : IsUnit x.reverse := hs.squarefree _ hPx
      have hxd : x.natDegree = 0 := by
        have h1 : x.reverse.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
        rwa [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hx0), Nat.sub_zero] at h1
      rw [eq_C_of_natDegree_eq_zero hxd]
      exact isUnit_C.mpr (IsUnit.mk0 _ hx0)
    rw [mul_comm]
    exact hrs.mul_unit (isUnit_C.mpr (IsUnit.mk0 _ hc))

end UpperTheory.Gal.LocalSmoothExtension
end

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOf_of :
    TestOf := by
  intro H _ K f hf
  obtain ⟨hbi, S, hS⟩ := hf
  have hinv : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g :=
    fun k hk k' hk' g => hbi ⟨k, hk⟩ ⟨k', hk'⟩ g
  refine ⟨⟨Subgroup.Commensurable.refl K, ?_, ?_, S, ?_⟩, hinv⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro k hk g
    exact hinv _ (K.inv_mem hk) _ hk g
  · intro g hg
    obtain ⟨s, hs, a, b, rfl⟩ := hS g hg
    exact ⟨s, hs, a, a.2, b, b.2, rfl⟩
end

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOne_of :
    TestOne := by
  intro p _ G
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.LKMid.isTest_indicator _ _ (by
      rintro _ ⟨k, hk, rfl⟩
      rw [GlobalTheory.LKCx.sigG_one]
      exact hk)
  · exact GlobalTheory.LKDef.HeckeTraceExample.indicator_bi _
end

section

set_option autoImplicit false

open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)
open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct Classical

private theorem map_oneP {p : ℕ} [Fact p.Prime] (σ : ℂ ≃+* ℂ) (G : HTGroup p) (x : Gr G 1) :
    σ (oneP G x) = oneP G x := by
  by_cases h : x ∈ (Kp G : Set (Gr G 1))
  · simp [oneP, Set.indicator_of_mem h]
  · simp [oneP, Set.indicator_of_notMem h]

private theorem dTrace_conj {p : ℕ} [Fact p.Prime] (hH : HeckeTraceSemi) (σ : ℂ ≃+* ℂ) (G : HTGroup p)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) (ξ' : Representation ℂ (G.Cˣ × ℚˣ) V') (e : V ≃+ V') (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) (K : Subgroup G.GAf) (f : G.GAf → ℂ) :
    dTrace G ξ' K (fun g => σ (f g)) (Kp G) (oneP G) = σ (dTrace G ξ K f (Kp G) (oneP G)) := by
  have hterm : ∀ B : DForm G, B.trace ξ' K (fun g => σ (f g)) (Kp G) (oneP G) = σ (B.trace ξ K f (Kp G) (oneP G)) := by
    intro B
    have h := hH σ (grp G B.β) (G.GAf × Gr G 1) V V' (ξ.comp (grp G B.β).subtype) (ξ'.comp (grp G B.β).subtype) e hs
      (fun g x => hi g.1 x) B.emb (K.prod (Kp G)) (fun h => f h.1 * oneP G h.2)
    have hF : (fun h : G.GAf × Gr G 1 => σ (f h.1 * oneP G h.2)) = fun h => σ (f h.1) * oneP G h.2 := by
      funext h
      rw [map_mul, map_oneP]
    rw [hF] at h
    exact h
  unfold dTrace
  have hm := σ.toAddEquiv.map_finsum (fun q : DFCls G => (Quot.out q).trace ξ K f (Kp G) (oneP G))
  calc _ = ∑ᶠ q : DFCls G, σ ((Quot.out q).trace ξ K f (Kp G) (oneP G)) := finsum_congr fun q => hterm _
    _ = _ := hm.symm

theorem UpperTheory.Gal.LocalSmoothExtension.specConj_of :
    TraceSemi → ConjRep → HeckeTraceSemi → GoodConj → SchWConj → PolyFnConj → SpecConj := by
  intro hT hCR hH hG hSW hP σ p _ D G L lam K J ψ θ f hS
  obtain ⟨hcomm, V, i1, i2, i3, ξ, hwt, hsp⟩ := hS
  obtain ⟨V', j1, j2, j3, ξ', e, hse, hint⟩ := hCR σ (G.Cˣ × ℚˣ) V ξ
  have hPf := hP σ G.GAf J K ψ f
  refine ⟨fun j j' w => ?_, V', j1, j2, j3, ξ', ?_, ?_⟩
  · rw [hPf.1, hPf.1, hcomm]
  · intro B y h1 h2
    rw [hSW, ← hwt B y h1 h2]
    exact hT σ V V' e hse (ξ y.1) (ξ' y.1) (fun x => hint y.1 x)
  · intro s' hs'
    obtain ⟨s, rfl⟩ : ∃ s : List J →₀ ℂ, wmap σ.toRingHom s = s' := by
      refine ⟨wmap σ.symm.toRingHom s', ?_⟩
      ext w
      simp [wmap]
    have hw : σ (wop θ s) = wop (fun j => σ (θ j)) (wmap σ.toRingHom s) :=
      UpperTheory.Gal.CertificateRingHomMap.map_wop_wmap σ.toRingHom σ.toRingHom (fun _ => rfl) θ s
    have hne : wop θ s ≠ 0 := by
      intro h0
      apply hs'
      rw [← hw, h0, map_zero]
    obtain ⟨a, hgood, htr⟩ := hsp s hne
    refine ⟨wmap σ.toRingHom a, ?_⟩
    have hc : polyFn K (fun j g => σ (ψ j g)) (wmul (wmap σ.toRingHom a) (wmap σ.toRingHom s)) (fun g => σ (f g)) =
        fun g => σ (polyFn K ψ (wmul a s) f g) := by
      rw [← hPf.2.2, hPf.2.1]
    rw [hc]
    refine ⟨hG σ p G K _ hgood, ?_⟩
    rw [dTrace_conj hH σ G ξ ξ' e hse hint]
    exact fun h0 => htr ((map_eq_zero σ).1 h0)
end

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cntSum_of :
    CntSum := by
  classical
  intro Γ _ K K' M h hMK hKK' hnorm hconj _ Δ _ r hrK hr V _ _ P hP
  have hPM : ∀ c ∈ K', ∀ u ∈ M, P (h * c * u) = P (h * c) := by
    intro c hc u hu
    have e := hP _ (hconj c hc u hu) c hc
    rw [← e]
    congr 1
    group
  let φ : (K' ⧸ K.subgroupOf K') × Δ → K' ⧸ M.subgroupOf K' := fun z =>
    QuotientGroup.mk (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨a, x⟩ ⟨a', x'⟩ he
      simp only [φ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at he
      push_cast at he
      have hK : (↑(Quotient.out a) : Γ)⁻¹ * ↑(Quotient.out a') ∈ K := by
        have e := K.mul_mem (K.mul_mem (hrK x) (hMK he)) (K.inv_mem (hrK x'))
        convert e using 1
        group
      have ha : a = a' := by
        rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a', QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        push_cast
        exact hK
      subst ha
      have hx1 : r x' * (r x')⁻¹ ∈ M := by simpa using M.one_mem
      have hx2 : r x' * (r x)⁻¹ ∈ M := by
        have e := hnorm (r x) (hKK' (hrK x)) _ he
        convert e using 1
        group
      obtain ⟨x0, _, hu⟩ := hr (r x') (hrK x')
      rw [hu x hx2, hu x' hx1]
    · intro b
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf K') c
      have hκ : (↑(Quotient.out (QuotientGroup.mk c : K' ⧸ K.subgroupOf K')) : Γ)⁻¹ * ↑c ∈ K := by
        rw [hk]
        push_cast
        have e := K.inv_mem (Subgroup.mem_subgroupOf.1 k.2)
        convert e using 1
        group
      obtain ⟨x, hx, -⟩ := hr _ hκ
      refine ⟨(QuotientGroup.mk c, x), ?_⟩
      simp only [φ]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      push_cast
      have e := hnorm (r x)⁻¹ (K'.inv_mem (hKK' (hrK x))) _ hx
      convert e using 1
      group
  haveI : Finite (K' ⧸ M.subgroupOf K') := Finite.of_surjective φ hφ.2
  letI : Fintype (K' ⧸ M.subgroupOf K') := Fintype.ofFinite _
  have hL : ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out z.1) * r z.2)
      = ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out (φ z))) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K')
      (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
    simp only [φ]
    rw [hu]
    push_cast
    have hc : (↑(Quotient.out z.1) : Γ) * r z.2 ∈ K' :=
      K'.mul_mem (Quotient.out z.1).2 (hKK' (hrK z.2))
    have e := hPM _ hc _ (Subgroup.mem_subgroupOf.1 u.2)
    rw [mul_assoc h, ← e]
    congr 1
    group
  let g : K' ⧸ M.subgroupOf K' → Γ ⧸ K := fun b => QuotientGroup.mk (h * ↑(Quotient.out b))⁻¹
  have hcnt : ∀ y : Γ ⧸ K, cntFn K K' M h (Quotient.out y)
      = ((Finset.univ.filter (fun b => g b = y)).card : ℂ) := by
    intro y
    have hset : (Finset.univ.filter fun b : K' ⧸ M.subgroupOf K' =>
        h * ↑(Quotient.out b) * Quotient.out y ∈ K) = Finset.univ.filter fun b => g b = y := by
      refine Finset.filter_congr fun b _ => ?_
      simp only [g]
      conv_rhs => rw [← QuotientGroup.out_eq' y]
      rw [QuotientGroup.eq, inv_inv]
    unfold cntFn
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hset]
  have hsupp : (Function.support fun y : Γ ⧸ K =>
      cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹) ⊆ ↑(Finset.univ.image g) := by
    intro y hy
    rw [Function.mem_support, hcnt] at hy
    by_contra hyn
    apply hy
    have e : Finset.univ.filter (fun b => g b = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hyn (Finset.mem_coe.2 (Finset.mem_image.2 ⟨b, Finset.mem_univ _, hb⟩))
    simp [e]
  have hR : ∑ y ∈ Finset.univ.image g, cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹
      = ∑ b, P (Quotient.out (g b))⁻¹ := by
    rw [Finset.sum_comp (fun y => P (Quotient.out y)⁻¹) g]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hcnt, Nat.cast_smul_eq_nsmul]
  have hR4 : ∑ b, P (Quotient.out (g b))⁻¹ = ∑ b : K' ⧸ M.subgroupOf K', P (h * ↑(Quotient.out b)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (h * ↑(Quotient.out b))⁻¹
    simp only [g]
    rw [hk, show ((h * ↑(Quotient.out b))⁻¹ * (↑k : Γ))⁻¹ = (↑k)⁻¹ * (h * ↑(Quotient.out b)) by group]
    exact hP _ (K.inv_mem k.2) _ (Quotient.out b).2
  rw [hL, Fintype.sum_bijective φ hφ (fun z => P (h * ↑(Quotient.out (φ z))))
    (fun b => P (h * ↑(Quotient.out b))) (fun _ => rfl), finsum_eq_sum_of_support_subset _ hsupp, hR, hR4]
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.Gen.BaseChange (down exists_gObjMap_pull spMap_comp')
open UpperTheory.Gal.Int.Geo (IsTrans)
open UpperTheory.Gal.LocalSmoothExtension

private theorem objMap_along {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj b N s'} {o : GObj b N s} {f g : S' ⟶ S}
    (e : f = g) (n : GObjMap o' o f) : ∃ n' : GObjMap o' o g, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

theorem UpperTheory.Gal.LocalSmoothExtension.legBc_of :
    MapEq → TransPull → LegBc := by
  intro hME hTP p _ D G L R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N N' M M' P P' f f' hf hf' m m' h π o ψ φ hπ hψ
  have hw : (f' ≫ π) ≫ M.s = P'.s ≫ spMap τ := by
    rw [Category.assoc, hπ]
    exact hf'.w
  obtain ⟨π₁, hπf, hπs⟩ : ∃ π₁ : P'.X ⟶ P.X, π₁ ≫ f = f' ≫ π ∧ π₁ ≫ P.s = P'.s :=
    ⟨hf.lift (f' ≫ π) P'.s hw, hf.lift_fst _ _ _, hf.lift_snd _ _ _⟩
  obtain ⟨o₁, ⟨φ₁⟩⟩ : ∃ o₁ : GObj gb₂ N P'.s, Nonempty (GObjMap o₁ P.univ π₁) := by
    have key := exists_gObjMap_pull π₁ P.univ
    rw [hπs] at key
    exact key
  let d₁ : GObj gb₁ N (P'.s ≫ spMap τ) := down hρ ht rfl o₁
  let φd : GObjMap d₁ (down hρ ht rfl P.univ) π₁ :=
    ⟨φ₁.φ, φ₁.φ₂, φ₁.cart, φ₁.sq, φ₁.act, φ₁.pol, φ₁.eta⟩
  obtain ⟨n, hn⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ (down hρ ht rfl P.univ) M.univ π₁ f m).1 φd
  obtain ⟨n', hn'⟩ := objMap_along hπf n
  obtain ⟨m'', hm''⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ o M.univ f' π φ).2 n'
  obtain ⟨ψ₁, hψ₁, hT⟩ := hTP p D G L R₁ gb₁ N N' _ _ M'.s (P'.s ≫ spMap τ) f' hf'.w M'.univ o
    (down hρ ht rfl P'.univ) d₁ m' m'' h ψ hψ
  obtain ⟨t₁, t₂, t₃, t₄, t₅⟩ := hT
  refine ⟨π₁, o₁, ψ₁, φ₁, hπs, ⟨t₁, t₂, t₃, t₄, fun k _ _ t β hβ => ?_⟩, hπf, ?_⟩
  · exact t₅ k t (β.comp τ) (by rw [spMap_comp', ← Category.assoc, hβ])
  · have e : φ₁.φ ≫ m.φ = m''.φ ≫ φ.φ := by
      rw [hm'', hn', hn]
      rfl
    calc (ψ₁.left ≫ φ₁.φ) ≫ m.φ = ψ₁.left ≫ φ₁.φ ≫ m.φ := Category.assoc _ _ _
      _ = ψ₁.left ≫ m''.φ ≫ φ.φ := congrArg (fun z => ψ₁.left ≫ z) e
      _ = (ψ₁.left ≫ m''.φ) ≫ φ.φ := (Category.assoc _ _ _).symm
      _ = m'.φ ≫ ψ.left ≫ φ.φ := by rw [hψ₁, Category.assoc]
end
