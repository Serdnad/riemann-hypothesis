module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem avg_abs {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V)
    (h : ∀ v, ∃ N : Subgroup K, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, ρ n v = v) :
    ∃ p : Module.End ℂ V, (∀ v u, ρ u (p v) = p v) ∧ (∀ v, (∀ u, ρ u v = v) → p v = v) ∧
      ∀ T : Module.End ℂ V, (∀ u, Commute T (ρ u)) → Commute T p := by
  classical
  obtain ⟨avg, havg⟩ : ∃ avg : Subgroup K → Module.End ℂ V,
      ∀ N, avg N = (N.index : ℂ)⁻¹ • ∑ᶠ q : K ⧸ N, ρ q.out := ⟨_, fun _ => rfl⟩
  have hform : ∀ (N : Subgroup K) [Fintype (K ⧸ N)] (v : V),
      avg N v = (N.index : ℂ)⁻¹ • ∑ q : K ⧸ N, ρ q.out v := by
    intro N _ v
    rw [havg, finsum_eq_sum_of_fintype, LinearMap.smul_apply, LinearMap.sum_apply]
  have hcard : ∀ (N : Subgroup K) [N.FiniteIndex] [Fintype (K ⧸ N)],
      (Fintype.card (K ⧸ N) : ℂ) = N.index ∧ (N.index : ℂ) ≠ 0 := by
    intro N _ _
    refine ⟨by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card], ?_⟩
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  have hlift : ∀ (N : Subgroup K) (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ g : K, ρ ((g : K ⧸ N).out) v = ρ g v := by
    intro N v hv g
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
    rw [hn, map_mul, Module.End.mul_apply, hv _ n.2]
  have hconj : ∀ (N : Subgroup K) [N.Normal] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ k : K, ∀ n ∈ N, ρ n (ρ k v) = ρ k v := by
    intro N hN v hv k n hn
    have h1 : k⁻¹ * n * k ∈ N := by
      simpa using hN.conj_mem n hn k⁻¹
    have h2 : n * k = k * (k⁻¹ * n * k) := by group
    rw [← Module.End.mul_apply, ← map_mul, h2, map_mul, Module.End.mul_apply, hv _ h1]
  have hinv : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ u : K, ρ u (avg N v) = avg N v := by
    intro N _ _ v hv u
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex

    rw [hform N v, map_smul, map_sum]
    congr 1
    have hq : ∀ q : K ⧸ N, ρ u (ρ q.out v) = ρ ((u • q).out) v := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [hlift N v hv, MulAction.Quotient.smul_mk, hlift N v hv, smul_eq_mul, map_mul,
          Module.End.mul_apply]
    simp only [hq]
    exact Equiv.sum_comp (MulAction.toPerm u) (fun q : K ⧸ N => ρ q.out v)
  have hfixed : ∀ (N : Subgroup K) [N.FiniteIndex] (v : V), (∀ u, ρ u v = v) → avg N v = v := by
    intro N _ v hv
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    rw [hform N v]
    simp only [hv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, (hcard N).1, inv_mul_cancel₀ (hcard N).2, one_smul]
  have hshift : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ k : K, avg N (ρ k v) = avg N v := by
    intro N _ _ v hv k
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    rw [hform N (ρ k v), hform N v]
    congr 1
    have hq : ∀ q : K ⧸ N, ρ q.out (ρ k v) = ρ ((q * (k : K ⧸ N)).out) v := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [hlift N _ (hconj N v hv k), ← QuotientGroup.mk_mul, hlift N v hv, map_mul,
          Module.End.mul_apply]
    simp only [hq]
    exact Equiv.sum_comp (Equiv.mulRight (k : K ⧸ N)) (fun q : K ⧸ N => ρ q.out v)
  let A : Submodule ℂ V := Submodule.span ℂ {x | ∃ k u, ρ k u - u = x}
  have hdiff : ∀ (N : Subgroup K) [N.FiniteIndex] (v : V), v - avg N v ∈ A := by
    intro N _ v
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    have e : v - avg N v = (N.index : ℂ)⁻¹ • ∑ q : K ⧸ N, (v - ρ q.out v) := by
      rw [hform N v, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, (hcard N).1, inv_mul_cancel₀ (hcard N).2, one_smul]
    rw [e]
    refine A.smul_mem _ (A.sum_mem fun q _ => ?_)
    rw [← neg_sub]
    exact A.neg_mem (Submodule.subset_span ⟨q.out, v, rfl⟩)
  have hcomm : ∀ (N : Subgroup K) [N.FiniteIndex] (T : Module.End ℂ V),
      (∀ u, Commute T (ρ u)) → ∀ v, T (avg N v) = avg N (T v) := by
    intro N _ T hT v
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex

    rw [hform N v, hform N (T v), map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Module.End.mul_apply, (hT q.out).eq, Module.End.mul_apply]
  have hkill : ∀ a ∈ A, ∃ N : Subgroup K, N.Normal ∧ N.FiniteIndex ∧
      ∀ N' : Subgroup K, N'.Normal → N'.FiniteIndex → N' ≤ N →
        (∀ n ∈ N', ρ n a = a) ∧ avg N' a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, u, rfl⟩ := hx
      obtain ⟨N, hN, hNf, hu⟩ := h u
      refine ⟨N, hN, hNf, fun N' hN' hN'f hle => ?_⟩
      have hu' : ∀ n ∈ N', ρ n u = u := fun n hn => hu n (hle hn)
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_sub, hconj N' u hu' k n hn, hu' n hn]
      · rw [map_sub, hshift N' u hu' k, sub_self]
    | zero =>
      refine ⟨⊤, inferInstance, inferInstance, fun N' _ _ _ => ⟨fun n _ => map_zero _, map_zero _⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1n, h1f, h1⟩ := hx
      obtain ⟨N2, h2n, h2f, h2⟩ := hy
      refine ⟨N1 ⊓ N2, inferInstance, inferInstance, fun N' hN' hN'f hle => ?_⟩
      obtain ⟨a1, b1⟩ := h1 N' hN' hN'f (hle.trans inf_le_left)
      obtain ⟨a2, b2⟩ := h2 N' hN' hN'f (hle.trans inf_le_right)
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_add (f := _), a1 n hn, a2 n hn]
      · rw [map_add (f := _), b1, b2, add_zero]
    | smul c x _ hx =>
      obtain ⟨N1, h1n, h1f, h1⟩ := hx
      refine ⟨N1, h1n, h1f, fun N' hN' hN'f hle => ?_⟩
      obtain ⟨a1, b1⟩ := h1 N' hN' hN'f hle
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_smul, a1 n hn]
      · rw [map_smul, b1, smul_zero]
  have hzero : ∀ w ∈ A, (∀ u, ρ u w = w) → w = 0 := by
    intro w hw hfix
    obtain ⟨N, hN, hNf, hN'⟩ := hkill w hw
    rw [← hfixed N w hfix]
    exact (hN' N hN hNf le_rfl).2
  choose Nv hNv hNvf hNvfix using h
  let pf : V → V := fun v => avg (Nv v) v
  have hagree : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      avg N v = pf v := by
    intro N _ _ v hv
    haveI := hNv v
    haveI := hNvf v
    rw [← sub_eq_zero]
    apply hzero
    · have e : avg N v - pf v = (v - pf v) - (v - avg N v) := by abel
      rw [e]
      exact A.sub_mem (hdiff _ v) (hdiff N v)
    · intro u
      rw [map_sub, hinv N v hv u, hinv (Nv v) v (hNvfix v) u]
  let p : Module.End ℂ V :=
    { toFun := pf
      map_add' := fun v w => by
        haveI := hNv v; haveI := hNvf v; haveI := hNv w; haveI := hNvf w
        have hv : ∀ n ∈ Nv v ⊓ Nv w, ρ n v = v := fun n hn => hNvfix v n hn.1
        have hw : ∀ n ∈ Nv v ⊓ Nv w, ρ n w = w := fun n hn => hNvfix w n hn.2
        have hvw : ∀ n ∈ Nv v ⊓ Nv w, ρ n (v + w) = v + w := fun n hn => by
          rw [map_add (f := _), hv n hn, hw n hn]
        rw [← hagree _ _ hvw, ← hagree _ _ hv, ← hagree _ _ hw, map_add (f := _)]
      map_smul' := fun c v => by
        haveI := hNv v; haveI := hNvf v
        have hcv : ∀ n ∈ Nv v, ρ n (c • v) = c • v := fun n hn => by
          rw [map_smul, hNvfix v n hn]
        rw [RingHom.id_apply, ← hagree _ _ hcv, map_smul] }
  refine ⟨p, fun v u => ?_, fun v hv => ?_, fun T hT => ?_⟩
  · haveI := hNv v; haveI := hNvf v
    exact hinv (Nv v) v (hNvfix v) u
  · haveI := hNvf v
    exact hfixed (Nv v) v hv
  · refine LinearMap.ext fun v => ?_
    haveI := hNv v; haveI := hNvf v
    have hTv : ∀ n ∈ Nv v, ρ n (T v) = T v := fun n hn => by
      rw [← Module.End.mul_apply, ← (hT n).eq, Module.End.mul_apply, hNvfix v n hn]
    show T (pf v) = pf (T v)
    rw [← hagree (Nv v) (T v) hTv]
    exact hcomm (Nv v) T hT v

theorem UpperTheory.V.Lit.Bor.avgProj :
    UpperTheory.V.Lit.Bor.AvgProj := by
  intro G V _ _ _ _ _ ρ U hU hopen
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let ρU : Representation ℂ U V := ρ.comp U.subtype
  have h : ∀ v, ∃ N : Subgroup U, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, ρU n v = v := by
    intro v
    let S : Subgroup U :=
      { carrier := {u | ρ (u : G) v = v}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hS : IsOpen (S : Set U) := (hopen v).preimage continuous_subtype_val
    haveI : Finite (U ⧸ S) := Subgroup.quotient_finite_of_isOpen S hS
    haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact ⟨S.normalCore, inferInstance, inferInstance, fun n hn => S.normalCore_le hn⟩
  obtain ⟨p, h1, h2, h3⟩ := avg_abs ρU h
  exact ⟨p, fun v u hu => h1 v ⟨u, hu⟩, fun v hv => h2 v (fun u => hv u u.2),
    fun T hT => h3 T (fun u => hT u u.2)⟩
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.indepAbs :
    UpperTheory.V.Lit.Bor.IndepAbs := by
  classical
  intro O W _ _ A s V h hs hn
  have hsup : ∀ P Q : Submodule ℂ W, (∀ o, ∀ x ∈ P, A o x ∈ P) → (∀ o, ∀ x ∈ Q, A o x ∈ Q) →
      ∀ o, ∀ x ∈ P ⊔ Q, A o x ∈ P ⊔ Q := by
    intro P Q hP hQ o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hP o y hy) (hQ o z hz)
  have hfs : ∀ t : Finset (Fin s), ∀ o, ∀ x ∈ t.sup V, A o x ∈ t.sup V := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro o x hx
      simp only [Finset.sup_empty, Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    | insert j t hj ih =>
      rw [Finset.sup_insert]
      exact hsup _ _ (h j) ih
  have key : ∀ t : Finset (Fin s), ∀ i, i ∉ t → Disjoint (V i) (t.sup V) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro i _; simp
    | insert j t hj ih =>
      intro i hi
      rw [Finset.mem_insert, not_or] at hi
      obtain ⟨hij, hit⟩ := hi
      have hSinv := hfs t
      have hiS := ih i hit
      have hjS := ih j hj
      rw [Finset.sup_insert, disjoint_iff]
      set S := t.sup V with hSdef
      by_cases hVi : V i = ⊥
      · rw [hVi, bot_inf_eq]
      have hM : ∀ o, ∀ x ∈ V i ⊓ (V j ⊔ S), A o x ∈ V i ⊓ (V j ⊔ S) :=
        fun o x hx => ⟨h i o x hx.1, hsup _ _ (h j) hSinv o x hx.2⟩
      rcases hs i _ inf_le_left hM with hbot | htop
      · exact hbot
      exfalso
      have hle : V i ≤ V j ⊔ S := inf_eq_left.mp htop
      have huniq : ∀ y y' : V j, ((y : W) - y') ∈ S → y = y' := by
        intro y y' hyy
        have h0 : ((y : W) - y') ∈ V j ⊓ S := ⟨sub_mem y.2 y'.2, hyy⟩
        rw [disjoint_iff.mp hjS, Submodule.mem_bot, sub_eq_zero] at h0
        exact Subtype.ext h0
      let fj : V j →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V j).subtype
      have hfj : Function.Injective fj := by
        intro a b hab
        exact huniq a b ((Submodule.Quotient.eq S).mp hab)
      let ej := LinearEquiv.ofInjective fj hfj
      let fi : V i →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V i).subtype
      have hrange : ∀ x : V i, fi x ∈ LinearMap.range fj := by
        intro x
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle x.2)
        refine ⟨⟨y, hy⟩, ?_⟩
        show S.mkQ y = S.mkQ x
        rw [← hyz, map_add (f := _), Submodule.mkQ_apply S z, (Submodule.Quotient.mk_eq_zero S).mpr hz,
          add_zero]
      let T : V i →ₗ[ℂ] V j := ej.symm.toLinearMap ∘ₗ (fi.codRestrict (LinearMap.range fj) hrange)
      have hT : ∀ x : V i, ((T x : W) - x) ∈ S := by
        intro x
        have e0 : T x = ej.symm ⟨fi x, hrange x⟩ := rfl
        have e1 := ej.apply_symm_apply ⟨fi x, hrange x⟩
        rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply, ← e0] at e1
        exact (Submodule.Quotient.eq S).mp e1
      have hTeq : ∀ o (x : V i), T ((A o).restrict (h i o) x) = (A o).restrict (h j o) (T x) := by
        intro o x
        apply huniq
        have e1 := hT ((A o).restrict (h i o) x)
        have e2 : A o ((T x : W) - x) ∈ S := hSinv o _ (hT x)
        have e3 : ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h j o) (T x) : W))
            = ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h i o) x : W))
              - A o ((T x : W) - x) := by
          simp only [LinearMap.restrict_coe_apply, map_sub]
          abel
        rw [e3]
        exact sub_mem e1 e2
      have hTinj : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        have e1 := hT x
        rw [hx, Submodule.coe_zero, zero_sub] at e1
        have hxS : (x : W) ∈ S := by simpa using S.neg_mem e1
        have e2 : (x : W) ∈ V i ⊓ S := ⟨x.2, hxS⟩
        rw [disjoint_iff.mp hiS, Submodule.mem_bot] at e2
        exact (Submodule.mem_bot ℂ).mpr (Subtype.ext e2)
      let N := (LinearMap.range T).map (V j).subtype
      have hNle : N ≤ V j := Submodule.map_subtype_le _ _
      have hNinv : ∀ o, ∀ x ∈ N, A o x ∈ N := by
        intro o x hx
        obtain ⟨y, ⟨z, rfl⟩, rfl⟩ := hx
        refine ⟨T ((A o).restrict (h i o) z), ⟨_, rfl⟩, ?_⟩
        rw [hTeq]
        rfl
      have hTsurj : Function.Surjective T := by
        rcases hs j N hNle hNinv with hN0 | hNj
        · exfalso
          obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVi
          have hmem : ((T ⟨x, hx⟩ : V j) : W) ∈ N := ⟨T ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩
          rw [hN0, Submodule.mem_bot] at hmem
          have : T ⟨x, hx⟩ = T 0 := by rw [map_zero]; exact Subtype.ext hmem
          exact hx0 (congrArg Subtype.val (hTinj this))
        · intro y
          have hy : (y : W) ∈ N := by rw [hNj]; exact y.2
          obtain ⟨y', ⟨z, rfl⟩, hz⟩ := hy
          exact ⟨z, Subtype.ext hz⟩
      exact hn i j hij ⟨LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩, hTeq⟩
  rw [iSupIndep_iff_supIndep]
  intro t u _ i _ hiu
  exact key u i hiu
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem basic_of_ne_zero {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    (κ : Kinf E a → Module.End ℂ M) (q : ℕ) :
    ∀ ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M, ω ≠ 0 → IsCochain κ ω →
      ∃ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), ω ≠ 0 ∧ IsCochain κ ω ∧ IsBasic ω := by
  let Z : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have hZ : ∀ k, adHerm k Z = Z := fun k => Subtype.ext (by
    change k.1 * 1 * star k.1 = 1
    rw [mul_one]; exact k.2.2)
  induction q with
  | zero => exact fun ω h0 h1 => ⟨0, ω, h0, h1, fun _ i => i.elim0⟩
  | succ q ih =>
    intro ω h0 h1
    by_cases hc : ω.curryLeft Z = 0
    · refine ⟨q + 1, ω, h0, h1, fun X i hi => ?_⟩
      have hi' : X i = Z := Subtype.ext hi
      have key : ∀ Y : Fin (q + 1) → Herm E a, Y 0 = Z → ω Y = 0 := fun Y hY => by
        have h := DFunLike.congr_fun hc (Fin.tail Y)
        have e : Matrix.vecCons Z (Fin.tail Y) = Y := by rw [← hY]; exact Fin.cons_self_tail Y
        rw [← e]
        exact h
      by_cases hi0 : (0 : Fin (q + 1)) = i
      · exact key X (hi0 ▸ hi')
      · have h := ω.map_swap X hi0
        rw [key _ (by simpa using hi')] at h
        exact neg_eq_zero.1 h.symm
    · refine ih _ hc fun k X => ?_
      change ω (Matrix.vecCons Z _) = κ k (ω (Matrix.vecCons Z X))
      rw [← h1]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [hZ]

theorem UpperTheory.V.Lit.Bor.basicEx :
    UpperTheory.V.Lit.Bor.BasicEx := by
  intro E _ _ _ a M _ _ _ _ κ L h
  rcases h with ⟨ω, h1, -, h0⟩ | ⟨q, ω, h1, -, h2⟩
  · exact basic_of_ne_zero κ 0 ω h0 h1
  · refine basic_of_ne_zero κ _ ω (fun h => h2 0 (fun k X => by simp) ?_) h1
    rw [h]
    exact AlternatingMap.ext fun X => by simp [dCo_apply]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem tr_one {R : Type} [CommRing R] {a : ℕ} (A B Z : Matrix (Fin a) (Fin a) R) :
    (A * (Z * B - B * Z)).trace = -(B * (Z * A - A * Z)).trace := by
  have h1 : (A * (Z * B)).trace = (B * (A * Z)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h2 : (B * (Z * A)).trace = (A * (B * Z)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_sub, Matrix.trace_sub, h1, h2]
  ring

private theorem trF_one {E : Type} [Field E] [NumberField E] {a : ℕ} (A B Z : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF A (Z * B - B * Z) = -trF B (Z * A - A * Z) := by
  unfold trF
  rw [tr_one, ← Finset.sum_neg_distrib]
  rfl

private theorem trF_neg {E : Type} [Field E] [NumberField E] {a : ℕ} (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF A (-B) = -trF A B := by
  unfold trF
  rw [Matrix.mul_neg, Matrix.trace_neg, ← Finset.sum_neg_distrib]
  rfl

theorem UpperTheory.V.Lit.Bor.frameBr :
    UpperTheory.V.Lit.Bor.FrameBr := by
  intro E _ _ _ a n e he N _ _
  refine ⟨fun β Z hZ => ?_, fun β X h => ?_⟩
  · have h1 : ∀ j, β (brH Z hZ (e j)) (e j) = ∑ k, trF (e k).1 (Z * (e j).1 - (e j).1 * Z) • β (e k) (e j) := by
      intro j
      conv_lhs => rw [he (brH Z hZ (e j))]

      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    have h2 : ∀ j, β (e j) (brH Z hZ (e j)) = ∑ k, trF (e k).1 (Z * (e j).1 - (e j).1 * Z) • β (e j) (e k) := by
      intro j
      conv_lhs => rw [he (brH Z hZ (e j))]

      simp only [map_sum, map_smul]
      rfl
    simp only [h1, h2]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [trF_one, neg_smul, neg_add_cancel]
  · have hb : ∀ j, (brH _ (h j) X).1 = -((Complex.I • X.1) * (e j).1 - (e j).1 * (Complex.I • X.1)) := by
      intro j
      change (Complex.I • (e j).1) * X.1 - X.1 * (Complex.I • (e j).1) = _
      simp only [Matrix.smul_mul, Matrix.mul_smul, neg_sub]
    have h1 : ∀ j, X.1 * (e j).1 - (e j).1 * X.1 =
        ∑ k, trF (e k).1 (brH _ (h j) X).1 • (Complex.I • (e k).1) := by
      intro j
      have h0 : (brH _ (h j) X).1 = ∑ k, trF (e k).1 (brH _ (h j) X).1 • (e k).1 := by
        conv_lhs => rw [he (brH _ (h j) X)]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      have h3 : X.1 * (e j).1 - (e j).1 * X.1 = Complex.I • (brH _ (h j) X).1 := by
        rw [hb]
        simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_smul,
          one_smul, neg_neg]
      rw [h3]
      conv_lhs => rw [h0]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have h2 : ∀ j, β (Complex.I • (e j).1) (brH _ (h j) X) =
        ∑ k, trF (e k).1 (brH _ (h j) X).1 • β (Complex.I • (e j).1) (e k) := by
      intro j
      conv_lhs => rw [he (brH _ (h j) X)]

      simp only [map_sum, map_smul]
    simp only [h1, h2]

    simp only [map_sum, LinearMap.map_smul β, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb, hb, trF_neg, trF_neg, trF_one, neg_smul]
end
