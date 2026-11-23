module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

noncomputable section

namespace UpperTheory.Gal.Gen

theorem hS_pf : HS := by
  classical
  intro X _ B V hV
  let L := WithLp.linearEquiv 2 ℂ (X → ℂ)
  let V' : Submodule ℂ (EuclideanSpace ℂ X) := V.map (L.symm : (X → ℂ) →ₗ[ℂ] EuclideanSpace ℂ X)
  have hfr : Module.finrank ℂ V' = Module.finrank ℂ V := LinearEquiv.finrank_map_eq L.symm V
  let e := stdOrthonormalBasis ℂ V'
  let f : Fin (Module.finrank ℂ V') → EuclideanSpace ℂ X := fun i => (e i : EuclideanSpace ℂ X)
  have hf : Orthonormal ℂ f := e.orthonormal.comp_linearIsometry V'.subtypeₗᵢ
  have hfix : ∀ i x, ∑ y, B x y * f i y = f i x := by
    intro i x
    obtain ⟨v, hv, hvf⟩ := (e i).2
    have h1 : ∀ y, f i y = v y := by
      intro y
      have : f i = L.symm v := hvf.symm
      rw [this]
      rfl
    have h2 := congrFun (hV v hv) x
    simp only [Matrix.mulVec, dotProduct] at h2
    simp only [h1]
    exact h2
  let r : X → EuclideanSpace ℂ X := fun x => WithLp.toLp 2 (fun y => starRingEnd ℂ (B x y))
  have hinner : ∀ i x, inner ℂ (r x) (f i) = f i x := by
    intro i x
    rw [← hfix i x, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [r, RCLike.inner_apply, mul_comm]
  have hbessel : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ ∑ y, ‖B x y‖ ^ 2 := by
    intro x
    have h := hf.sum_inner_products_le (x := r x) (s := Finset.univ)
    have h3 : ‖r x‖ ^ 2 = ∑ y, ‖B x y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [r]
    rw [h3] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_inner_symm, hinner]
  have hone : ∀ i, ∑ x, ‖f i x‖ ^ 2 = 1 := by
    intro i
    rw [← EuclideanSpace.norm_sq_eq, hf.1 i]
    simp
  calc (Module.finrank ℂ V : ℝ) = ∑ i : Fin (Module.finrank ℂ V'), ∑ x, ‖f i x‖ ^ 2 := by
        simp [hone, hfr]
    _ = ∑ x, ∑ i, ‖f i x‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ x, ∑ y, ‖B x y‖ ^ 2 := Finset.sum_le_sum fun x _ => hbessel x

end UpperTheory.Gal.Gen

end
end

section

open Module

namespace UpperTheory.Gal.Gen

private theorem exists_invariant_flag_mod_l (hF : FixVec) (l : ℕ) [Fact l.Prime] (H : Type) [Group H] (hH : IsPGroup l H)
    (V : Type) [AddCommGroup V] [Module (ZMod l) V] [Finite V] (ρ : Representation (ZMod l) H V)
    (m : ℕ) (hm : m ≤ finrank (ZMod l) V) :
    ∃ v : Fin m → V, LinearIndependent (ZMod l) v ∧
      ∀ h j, ρ h (v j) - v j ∈ Submodule.span (ZMod l) (v '' {i | i < j}) := by
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  induction m with
  | zero =>
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun _ j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hs⟩ := ih (Nat.le_of_succ_le hm)
    set U := Submodule.span (ZMod l) (Set.range v) with hU
    have hmono : ∀ j, Submodule.span (ZMod l) (v '' {i | i < j}) ≤ U := fun j =>
      Submodule.span_mono (Set.image_subset_range _ _)
    have hvU : ∀ j, v j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
    have hst : ∀ h, ∀ u ∈ U, ρ h u ∈ U := by
      intro h u hu
      have hle : U ≤ U.comap (ρ h) := by
        rw [hU, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have h1 := hmono j (hs h j)
        have h2 := U.add_mem h1 (hvU j)
        simpa using h2
      exact hle hu
    have hne : U ≠ ⊤ := by
      intro htop
      have h1 : finrank (ZMod l) U = m := by
        rw [hU, finrank_span_eq_card hv]; simp
      rw [htop, finrank_top] at h1
      omega
    obtain ⟨x, hx, hxs⟩ := hF l H hH V ρ U hst hne
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · exact (linearIndependent_finSnoc).2 ⟨hv, hx⟩
    · intro h j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · have himg : (Fin.snoc v x : Fin (m+1) → V) '' {i | i < Fin.last m} = Set.range v := by
          ext y
          constructor
          · rintro ⟨i, hi, rfl⟩
            have hi' : i ≠ Fin.last m := ne_of_lt hi
            obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi'
            exact ⟨i', by simp⟩
          · rintro ⟨i, rfl⟩
            exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp⟩
        simp only [Fin.snoc_last]
        rw [himg]
        exact hxs h
      · have himg : v '' {i | i < j} ⊆ (Fin.snoc v x : Fin (m+1) → V) '' {i | i < j.castSucc} := by
          rintro _ ⟨i, hi, rfl⟩
          exact ⟨i.castSucc, by simpa using hi, by simp⟩
        simp only [Fin.snoc_castSucc]
        exact Submodule.span_mono himg (hs h j)

theorem flag_pf : FixVec → Flag := by
  intro hF l _ H _ hH V _ _ _ ρ
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  obtain ⟨v, hv, hs⟩ := exists_invariant_flag_mod_l hF l H hH V ρ _ le_rfl
  have hsp : ⊤ ≤ Submodule.span (ZMod l) (Set.range v) :=
    (hv.span_eq_top_of_card_eq_finrank' (by simp)).ge
  let b : Basis (Fin (finrank (ZMod l) V)) (ZMod l) V := Basis.mk hv hsp
  refine ⟨b, ?_⟩
  intro h i j hji
  have hb : ∀ j, b j = v j := fun j => Basis.mk_apply hv hsp j
  have hmem : ρ h (b j) - b j ∈ Submodule.span (ZMod l) (b '' {i | i < j}) := by
    have : (b : _ → V) '' {i | i < j} = v '' {i | i < j} := by
      ext y; simp [hb]
    rw [this, hb]
    exact hs h j
  have hsupp := (Basis.mem_span_image b).1 hmem
  by_contra hne
  have hi : i ∈ ((b.repr (ρ h (b j) - b j)).support : Set _) := by
    simpa using hne
  have := hsupp hi
  exact absurd this (not_lt.2 hji)

end UpperTheory.Gal.Gen
end

section

noncomputable section

namespace UpperTheory.Gal.Gen

private theorem exists_close_vector_ultrametric (k : Type) [NormedField k] [IsUltrametricDist k] (X : Type) [Fintype X] (r : ℝ) :
    ∀ (n : ℕ) (P : Submodule k (X → k)) (v : X → k), Module.finrank k P = n →
      (∀ a : X → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) → ‖∑ i, a i * v i‖ ≤ r) →
      ∃ c ∈ P, ∀ i, ‖v i - c i‖ ≤ r := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P v hn h
  by_cases hP : P = ⊥
  · subst hP
    refine ⟨0, Submodule.zero_mem _, fun i => ?_⟩
    have key := h (Pi.single i 1) ?_ ?_
    · simpa [Pi.single_apply] using key
    · intro j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · intro c hc
      have hc0 : c = 0 := by simpa using hc
      simp [hc0]
  · obtain ⟨p0, hp0, hp0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hex : ∃ i, p0 i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hp0ne (funext hcon)
    obtain ⟨j, hj⟩ := hex
    haveI : Nonempty X := ⟨j⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => ‖p0 i‖)
    have hne : p0 i0 ≠ 0 := by
      intro h0
      have h1 := hi0 j
      rw [h0, norm_zero] at h1
      exact hj (norm_le_zero_iff.mp h1)
    obtain ⟨p, hp⟩ : ∃ p, p = (p0 i0)⁻¹ • p0 := ⟨_, rfl⟩
    have hpP : p ∈ P := hp ▸ P.smul_mem _ hp0
    have hpi0 : p i0 = 1 := by simp [hp, hne]
    have hple : ∀ i, ‖p i‖ ≤ 1 := by
      intro i
      simp only [hp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hne)]
      simpa using hi0 i
    obtain ⟨P', hP'⟩ : ∃ P', P' = P ⊓ LinearMap.ker (LinearMap.proj i0 : (X → k) →ₗ[k] k) := ⟨_, rfl⟩
    have hmem : ∀ c, c ∈ P' ↔ c ∈ P ∧ c i0 = 0 := by
      intro c
      simp [hP', Submodule.mem_inf, LinearMap.mem_ker]
    have hlt : P' < P := by
      refine lt_of_le_of_ne (fun c hc => ((hmem c).1 hc).1) ?_
      intro heq
      have h1 : p ∈ P' := heq ▸ hpP
      have h2 := ((hmem p).1 h1).2
      rw [hpi0] at h2
      exact one_ne_zero h2
    have hfr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨c', hc', hb⟩ := ih _ (hn ▸ hfr) P' (v - v i0 • p) rfl (by
      intro a ha hperp
      obtain ⟨s, hs⟩ : ∃ s, s = ∑ i, a i * p i := ⟨_, rfl⟩
      have hsn : ‖s‖ ≤ 1 := by
        rw [hs]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_one₀ (ha i) (norm_nonneg _) (hple i)
      have hsingle : ∀ w : X → k, ∑ i, (Pi.single i0 s : X → k) i * w i = s * w i0 := by
        intro w
        simp [Pi.single_apply, ite_mul]
      have key := h (a - Pi.single i0 s : X → k) ?_ ?_
      · have e : ∑ i, (a - Pi.single i0 s : X → k) i * v i = ∑ i, a i * (v - v i0 • p) i := by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub,
            Finset.sum_sub_distrib, hsingle]
          congr 1
          rw [hs, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rwa [e] at key
      · intro i
        by_cases hi : i = i0
        · subst hi
          simp only [Pi.sub_apply, Pi.single_eq_same]
          rw [sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha _) ?_)
          rwa [norm_neg]
        · simpa [Pi.single_apply, hi] using ha i
      · intro c hc
        have hd : c - c i0 • p ∈ P' := by
          refine (hmem _).2 ⟨P.sub_mem hc (P.smul_mem _ hpP), ?_⟩
          simp [hpi0]
        have h0 := hperp _ hd
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib] at h0
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hsingle]
        have h1 : ∑ i, a i * (c i0 * p i) = c i0 * s := by
          rw [hs, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [h1] at h0
        rw [mul_comm s]
        exact h0)
    refine ⟨v i0 • p + c', P.add_mem (P.smul_mem _ hpP) ((hmem _).1 hc').1, fun i => ?_⟩
    have e : v i - (v i0 • p + c') i = (v - v i0 • p) i - c' i := by
      simp [sub_sub]
    rw [e]
    exact hb i

theorem hB_pf : HB := by
  intro k _ _ X _ P v r h
  exact exists_close_vector_ultrametric k X r _ P v rfl h

end UpperTheory.Gal.Gen

end
end

section

open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.alg_pf :
    UpperTheory.Gal.Gen.HB → UpperTheory.Gal.Gen.GroupDet → UpperTheory.Gal.Gen.Alg := by
  intro hHB hGD k _ _ l _ H _ _ hH P hP hN
  classical
  have hl0 : 0 ≤ ‖(l : k)‖ := norm_nonneg _
  have hl1 : ‖(l : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k l
  have hdN : Module.finrank k P ≤ Fintype.card H := by
    have h := Submodule.finrank_le P
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have key : ∀ a : H → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) →
      ‖∑ i, a i * (fun _ => (1 : k)) i‖ ≤ Real.sqrt ‖(l : k)‖ := by
    intro a ha hperp
    have hker : P ≤ LinearMap.ker
        (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin := by
      intro c hc
      rw [LinearMap.mem_ker]
      funext g
      have h0 := hperp (fun h => c (h * g)) (hP c hc g)
      have h1 : ∑ h, a (h * g⁻¹) * c h = ∑ i, a i * c (i * g) :=
        Fintype.sum_equiv (Equiv.mulRight g⁻¹) _ _ (fun x => by simp)
      change ∑ h, a (h * g⁻¹) * c h = 0
      rw [h1]
      exact h0
    have hrank : (Matrix.of fun h g : H => a (h * g⁻¹)).rank ≤
        Fintype.card H - Module.finrank k P := by
      have h2 := LinearMap.finrank_range_add_finrank_ker
        (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at h2
      have h3 := Submodule.finrank_mono hker
      rw [← Matrix.rank_transpose]
      have h4 : (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.rank =
          Module.finrank k (LinearMap.range
            (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin) := (Matrix.finrank_range_mulVecLin _).symm
      omega
    have h1 := hGD k l H hH a _ ha hrank
    rw [Nat.sub_sub_self hdN] at h1
    simp only [mul_one]
    rw [Real.le_sqrt (norm_nonneg _) hl0]
    have hne : Fintype.card H ≠ 0 := Fintype.card_ne_zero
    refine (pow_le_pow_iff_left₀ (by positivity) hl0 hne).mp ?_
    calc (‖∑ i, a i‖ ^ 2) ^ Fintype.card H
        = (‖∑ i, a i‖ ^ Fintype.card H) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (‖(l : k)‖ ^ Module.finrank k P) ^ 2 := by gcongr
      _ = ‖(l : k)‖ ^ (2 * Module.finrank k P) := by rw [← pow_mul, mul_comm]
      _ ≤ ‖(l : k)‖ ^ Fintype.card H := pow_le_pow_of_le_one hl0 hl1 hN
  obtain ⟨c, hc, hcv⟩ := hHB k H P (fun _ => 1) (Real.sqrt ‖(l : k)‖) key
  refine ⟨c, hc, fun h => ?_⟩
  have h5 : ‖(1 : k) - c h‖ ≤ Real.sqrt ‖(l : k)‖ := hcv h
  exact (Real.le_sqrt (norm_nonneg _) hl0).mp h5
end
