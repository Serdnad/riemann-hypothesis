module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem UpperTheory.V.Fr.add_mul_self_eq_of_orthogonal_idempotents {C K : Type} [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
    (hn : n = 2 ∨ n = 3) (A : Subalgebra C (Matrix (Fin n) (Fin n) K)) (h2 : IsUnit (2 : C))
    (hY : Matrix.diagonal (fun i => (w n i : K)) ∈ A) (i : Fin n) : Matrix.single i i (1 : K) ∈ A := by
  have key : ∀ M : Matrix (Fin n) (Fin n) K, (2 : C) • M ∈ A → M ∈ A := by
    intro M hM
    have := A.smul_mem hM (↑h2.unit⁻¹ : C)
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  have hYY := A.mul_mem hY hY
  rcases hn with rfl | rfl
  · apply key
    fin_cases i
    · have e : (2 : C) • Matrix.single (0 : Fin 2) 0 (1 : K) = 1 + Matrix.diagonal (fun i => (w 2 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.add_mem A.one_mem hY
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (1 : Fin 2) 1 (1 : K) = 1 - Matrix.diagonal (fun i => (w 2 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.sub_mem A.one_mem hY
      rw [← e] at h
      exact h
  · apply key
    fin_cases i
    · have e : (2 : C) • Matrix.single (0 : Fin 3) 0 (1 : K) =
          Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K)) +
            Matrix.diagonal (fun i => (w 3 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.single_apply] <;> norm_num
      have h := A.add_mem hYY hY
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (1 : Fin 3) 1 (1 : K) =
          (2 : C) • (1 - Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K))) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.smul_mem (A.sub_mem A.one_mem hYY) (2 : C)
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (2 : Fin 3) 2 (1 : K) =
          Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K)) -
            Matrix.diagonal (fun i => (w 3 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.single_apply] <;> norm_num
      have h := A.sub_mem hYY hY
      rw [← e] at h
      exact h

theorem UpperTheory.V.Fr.idem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F n K), Integral O C ρ → ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range ρ.r) := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ ρ hI i
  haveI : CharP (ResidueField O) l := IsCoef.char
  have hunit : ∀ x : C, res O C x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra h
    exact hx ((res_eq_zero_iff O C x).2 ((IsLocalRing.mem_maximalIdeal x).2 h))
  have h2 : IsUnit (2 : C) := by
    apply hunit
    rw [map_ofNat]
    intro h0
    have h0' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h0'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).1 h0')
  obtain ⟨ζ, hζr, hζ⟩ := hI.ze
  have hζu : IsUnit ζ := by
    apply hunit
    rw [hζr]
    intro h0
    apply hF.baseSubgroup_spec
    rw [sub_eq_zero] at h0
    try simp only [← Units.val_inv_eq_inv_val] at h0
    have hx : F.Ψ ↑F.g0 = (F.Ψ ↑F.g0)⁻¹ := Units.ext h0
    calc F.Ψ ↑F.g0 ^ 2 = F.Ψ ↑F.g0 * F.Ψ ↑F.g0 := sq _
      _ = F.Ψ ↑F.g0 * (F.Ψ ↑F.g0)⁻¹ := by rw [← hx]
      _ = 1 := mul_inv_cancel _
  have hD : ρ.r F.g0 - ρ.r (F.star F.g0) = ζ • Matrix.diagonal (fun i => (w n i : K)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, Algebra.smul_def, hζ a]
      ring
    · rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab, smul_zero]
      exact ρ.diag a b hab
  have hspan : (Algebra.adjoin C (Set.range ρ.r)).toSubmodule = Submodule.span C (Set.range ρ.r) := by
    rw [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq]
  have hmem : ρ.r F.g0 - ρ.r (F.star F.g0) ∈ Submodule.span C (Set.range ρ.r) :=
    Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hY : Matrix.diagonal (fun i => (w n i : K)) ∈ Algebra.adjoin C (Set.range ρ.r) := by
    rw [← Subalgebra.mem_toSubmodule, hspan]
    have h := Submodule.smul_mem _ (↑hζu.unit⁻¹ : C) hmem
    rwa [hD, smul_smul, IsUnit.val_inv_mul, one_smul] at h
  rw [← hspan, Subalgebra.mem_toSubmodule]
  exact UpperTheory.V.Fr.add_mul_self_eq_of_orthogonal_idempotents hn _ h2 hY i
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.oddm :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (a g : ℕ) (G : MvPowerSeries (Fin a ⊕ Fin g) O), G ∈ wtPart O (Space.Loc.par a g) 1 → (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) G ∈ maximalIdeal O) → ∃ M : Fin g → MvPowerSeries (Fin a ⊕ Fin g) O, (∀ j, MvPowerSeries.constantCoeff (M j) ∈ maximalIdeal O) ∧ G = ∑ j, M j * MvPowerSeries.X (.inr j) := by
  classical
  intro O _ _ a g G hG hlin
  let M : Fin g → MvPowerSeries (Fin a ⊕ Fin g) O := fun j m =>
    if ∀ k : Fin g, k < j → m (Sum.inr k) = 0 then
      MvPowerSeries.coeff (m + Finsupp.single (Sum.inr j) 1) G else 0
  have hM : ∀ j m, MvPowerSeries.coeff m (M j) =
      if ∀ k : Fin g, k < j → m (Sum.inr k) = 0 then
        MvPowerSeries.coeff (m + Finsupp.single (Sum.inr j) 1) G else 0 := fun _ _ => rfl
  refine ⟨M, ?_, ?_⟩
  · intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hM]
    simpa using hlin (Sum.inr j)
  · ext n

    rw [map_sum]
    simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one, hM]
    by_cases hex : ∃ j : Fin g, n (Sum.inr j) ≠ 0
    · let S := Finset.univ.filter (fun j : Fin g => n (Sum.inr j) ≠ 0)
      have hS : S.Nonempty := by
        obtain ⟨j, hj⟩ := hex
        exact ⟨j, by simp [S, hj]⟩
      have hj0 : n (Sum.inr (S.min' hS)) ≠ 0 := by
        have := S.min'_mem hS
        simpa [S] using this
      have hmin : ∀ k : Fin g, n (Sum.inr k) ≠ 0 → S.min' hS ≤ k := fun k hk =>
        S.min'_le k (by simp [S, hk])
      have hle : ∀ j : Fin g, n (Sum.inr j) ≠ 0 → Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n := by
        intro j hj
        rw [Finsupp.single_le_iff]
        omega
      rw [Finset.sum_eq_single (S.min' hS)]
      · rw [if_pos (hle _ hj0), if_pos, tsub_add_cancel_of_le (hle _ hj0)]
        intro k hk
        by_contra hne
        have := hmin k (by simpa [Finsupp.tsub_apply, Finsupp.single_apply, ne_of_gt hk] using hne)
        exact absurd hk (not_lt.mpr this)
      · intro j _ hj
        by_cases hjl : Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n
        · rw [if_pos hjl]
          have hnj : n (Sum.inr j) ≠ 0 := by
            have := hjl (Sum.inr j)
            simp at this
            omega
          have hlt : S.min' hS < j := lt_of_le_of_ne (hmin j hnj) (Ne.symm hj)
          rw [if_neg]
          intro hall
          have := hall _ hlt
          simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm (ne_of_lt hlt)] at this
          exact hj0 this
        · rw [if_neg hjl]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hex
      have hz : ∀ j : Fin g, ¬ Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n := by
        intro j hj
        have := hj (Sum.inr j)
        simp [hex j] at this
      simp only [hz, if_false, Finset.sum_const_zero]
      apply hG
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero]
      · decide
      · intro i _
        rcases i with i | i
        · simp [Space.Loc.par]
        · simp [hex i]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem max_map {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C] [IsCO O C]
    {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] (φ : C →ₐ[O] C') {c : C} (hc : c ∈ maximalIdeal C) :
    φ c ∈ maximalIdeal C' := by
  rwa [← res_eq_zero_iff O, UpperTheory.V.Alg.res_map φ, res_eq_zero_iff]

private theorem pow_map {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C] [IsCO O C]
    {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] (φ : C →ₐ[O] C') (N : ℕ) {c : C}
    (hc : c ∈ maximalIdeal C ^ N) : φ c ∈ maximalIdeal C' ^ N := by
  have h : (maximalIdeal C).map φ ≤ maximalIdeal C' := Ideal.map_le_iff_le_comap.2 fun _ h => max_map φ h
  have h2 := Ideal.mem_map_of_mem φ hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h N h2

private theorem span_map {C C' K K' : Type} [CommRing C] [CommRing C'] [CommRing K] [CommRing K'] [Algebra C K]
    [Algebra C' K'] (φ : C → C') (f : K →+* K') (h : ∀ c, f (algebraMap C K c) = algebraMap C' K' (φ c))
    {s : Set K} {M : Submodule C' K'} (hs : ∀ x ∈ s, f x ∈ M) {x : K} (hx : x ∈ Submodule.span C s) : f x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add f]; exact add_mem hx hy
  | smul a x _ hx => rw [Algebra.smul_def, map_mul, h, ← Algebra.smul_def]; exact M.smul_mem _ hx

private theorem lc_of {X A B : Type} [TopologicalSpace X] {u : X → A} {v : X → B} (hu : IsLocallyConstant u)
    (h : ∀ x y, u x = u y → v x = v y) : IsLocallyConstant v := by
  rw [IsLocallyConstant.iff_eventually_eq] at hu ⊢
  exact fun x => (hu x).mono fun y hy => h _ _ hy

theorem UpperTheory.V.Fr.frobenius_corner_cone_map :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (K' : Type) [CommRing K'] [Algebra C' K'] (β : C →ₐ[O] C') (f : K →+* K'), (∀ c, f (algebraMap C K c) = algebraMap C' K' (β c)) → ∀ ρ : NRep F n K, Cone O C ρ → Cone O C' (ρ.map f) := by
  intro l _ O _ _ F n C _ _ _ K _ _ C' _ _ _ K' _ _ φ f h ρ H
  have hsp : ∀ i j, ∀ x ∈ Submodule.span C (Set.range fun g => ρ.r g i j),
      f x ∈ Submodule.span C' (Set.range fun g => (ρ.map f).r g i j) := fun i j x hx =>
    span_map φ f h (by rintro _ ⟨g, rfl⟩; exact Submodule.subset_span ⟨g, rfl⟩) hx
  refine ⟨fun g i => ?_, fun L hL hs => ?_, fun i j => ?_, fun i j N => ?_, ?_⟩
  · obtain ⟨c, h1, h2⟩ := H.dg g i
    exact ⟨φ c, by rw [← h, h1, NRep.map_r], by rw [UpperTheory.V.Alg.res_map, h2]⟩
  · obtain ⟨c, h1, h2⟩ := H.cyc L hL hs
    refine ⟨φ c, max_map φ h1, ?_⟩
    rw [← h, h2, map_list_prod, List.map_map]
    rfl
  · classical
    obtain ⟨t, ht⟩ := H.fg i j
    refine ⟨t.image f, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact hsp i j x (ht ▸ Submodule.subset_span hx)
    · rintro _ ⟨g, rfl⟩
      refine span_map φ f h (s := (t : Set K)) (fun x hx => Submodule.subset_span ?_) (x := ρ.r g i j) ?_
      · exact Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)
      · rw [ht]; exact Submodule.subset_span ⟨g, rfl⟩
  · refine lc_of (H.cont i j N) fun x y hxy => ?_
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hxy ⊢
    rw [NRep.map_r, NRep.map_r, ← map_sub]
    refine Submodule.smul_induction_on hxy (fun a ha z hz => ?_) (fun a b ha hb => ?_)
    · rw [Algebra.smul_def a z, map_mul, h, ← Algebra.smul_def (φ a) (f z)]
      exact Submodule.smul_mem_smul (pow_map φ N ha) (hsp i j z hz)
    · rw [map_add f]; exact add_mem ha hb
  · obtain ⟨χ, h1, h2⟩ := H.psi
    refine ⟨fun v i g => φ (χ v i g), fun v i => ⟨fun N => ?_, fun g => ?_⟩, fun v i g => ?_⟩
    · refine lc_of ((h1 v i).1 N) fun x y hxy => ?_
      rw [Ideal.Quotient.eq] at hxy ⊢
      rw [← map_sub]
      exact pow_map φ N hxy
    · rw [UpperTheory.V.Alg.res_map, (h1 v i).2]
    · rw [← h, h2, NRep.map_ψ]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem alg_of_rel {R D : Type} [CommRing R] [CommRing D] [IsDomain D] [Algebra R D]
    (T : Subalgebra R D) {x c d : D} {p : ℕ} (hp : 0 < p) (hc : c ∈ T) (hd : d ∈ T) (h0 : c ≠ 0)
    (h : x ^ p * c = d) : IsAlgebraic T x := by
  refine IsAlgebraic.of_pow hp ?_
  have hc' : (⟨c, hc⟩ : T) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  refine IsAlgebraic.of_smul (y := (⟨c, hc⟩ : T)) (mem_nonZeroDivisors_of_ne_zero hc') ?_
  have : (⟨c, hc⟩ : T) • x ^ p = algebraMap T D ⟨d, hd⟩ := by
    rw [Algebra.smul_def, mul_comm]; exact h
  rw [this]
  exact isAlgebraic_algebraMap _

private theorem trdeg_le_one {R D ι : Type} [CommRing R] [CommRing D] [IsDomain D] [Algebra R D]
    [FaithfulSMul R D] (x : ι → D) (wt : ι → ℤ) (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (h0 : ∀ (i j : ι) (p q : ℕ), p * wt i + q * wt j = 0 → x i ^ p * x j ^ q ∈ Set.range (algebraMap R D))
    {a b : ι} (ha : 0 < wt a) (hb : wt b < 0) (ha0 : x a ≠ 0) (hb0 : x b ≠ 0) : Algebra.trdeg R D ≤ 1 := by
  set T : Subalgebra R D := Algebra.adjoin R {x a} with hT
  have haT : x a ∈ T := Algebra.subset_adjoin rfl
  have hR : ∀ {y}, y ∈ Set.range (algebraMap R D) → y ∈ T := by
    rintro _ ⟨r, rfl⟩; exact T.algebraMap_mem r
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hb.le)
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hq' : wt b = -q := by omega
  have key : ∀ i, IsAlgebraic T (x i) := by
    intro i
    rcases le_total (wt i) 0 with h | h
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h)
      have hm' : wt i = -m := by omega
      exact alg_of_rel T hp0 (pow_mem haT m) (hR (h0 i a p m (by rw [hm', hp]; ring))) (pow_ne_zero _ ha0) rfl
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h
      have h1 := hR (h0 i b q m (by rw [hm, hq']; ring))
      have h2 := hR (h0 b a p q (by rw [hp, hq']; ring))
      refine alg_of_rel T (mul_pos hq0 hp0) (pow_mem h2 m) (mul_mem (pow_mem h1 p) (pow_mem haT (q * m)))
        (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ ha0))) (by ring)
  have hall : Algebra.IsAlgebraic T D := ⟨fun y => by
    have hy : y ∈ Algebra.adjoin R (Set.range x) := hgen ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact key i
    | algebraMap r => exact isAlgebraic_algebraMap (⟨_, T.algebraMap_mem r⟩ : T)
    | add y z _ _ h1 h2 => exact h1.add h2
    | mul y z _ _ h1 h2 => exact h1.mul h2⟩
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk R ({x a} : Set D)

private theorem trdeg_quot_le_one {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (η : Ideal A) (hη : η.IsPrime) (x : ι → A) (wt : ι → ℤ) (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (h0 : ∀ (i j : ι) (p q : ℕ), p * wt i + q * wt j = 0 → x i ^ p * x j ^ q ∈ Set.range (algebraMap R A))
    {a b : ι} (ha : 0 < wt a) (hb : wt b < 0) (ha0 : x a ∉ η) (hb0 : x b ∉ η) :
    Algebra.trdeg (R ⧸ η.comap (algebraMap R A)) (A ⧸ η) ≤ 1 := by
  refine trdeg_le_one (fun s => Ideal.Quotient.mk η (x s)) wt ?_ ?_ ha hb
    (fun e => ha0 (Ideal.Quotient.eq_zero_iff_mem.1 e)) (fun e => hb0 (Ideal.Quotient.eq_zero_iff_mem.1 e))
  · rw [eq_top_iff]
    intro y hy
    clear hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy : y ∈ Algebra.adjoin R (Set.range x) := hgen ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (Ideal.Quotient.mk (η.comap (algebraMap R A)) r)
    | add y z _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | mul y z _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2
  · intro i j p q h
    obtain ⟨r, hr⟩ := h0 i j p q h
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [← map_pow, ← map_pow, ← map_mul, ← hr]
    rfl

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

theorem UpperTheory.V.Fr.fibre :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η : Ideal S.A, η.IsPrime → S.u.OffTri η → S.td η ≤ 1 := by
  intro l _ O _ _ _ _ F C₀ n _ _ S η hη hoff
  obtain ⟨h1, h2⟩ := hoff
  have hb : ∃ g i j, j < i ∧ S.u.r g i j ∉ η := by
    by_contra h
    push Not at h
    exact h1 (Ideal.span_le.2 (by rintro _ ⟨g, i, j, hij, rfl⟩; exact h g i j hij))
  have ha : ∃ g i j, i < j ∧ S.u.r g i j ∉ η := by
    by_contra h
    push Not at h
    exact h2 (Ideal.span_le.2 (by rintro _ ⟨g, i, j, hij, rfl⟩; exact h g i j hij))
  obtain ⟨g, i, j, hij, hg⟩ := ha
  obtain ⟨g', i', j', hij', hg'⟩ := hb
  refine trdeg_quot_le_one (ι := F.G0 × Fin n × Fin n) η hη (fun s => S.u.r s.1 s.2.1 s.2.2)
    (fun s => w n s.2.1 - w n s.2.2) ?_ ?_ (a := (g, i, j)) (b := (g', i', j'))
    (sub_pos.2 (w_lt hij)) (sub_neg.2 (w_lt hij')) hg hg'
  · rw [eq_top_iff]
    rintro ⟨y, hy⟩ hy'
    clear hy'
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · exact Subalgebra.algebraMap_mem _ (⟨y, hy⟩ : S.B)
      · exact Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (algebraMap O S.B r)
    | add y z hy hz h1 h2 => exact add_mem h1 h2
    | mul y z hy hz h1 h2 => exact mul_mem h1 h2
  · intro s t p q h
    have hm : S.ρ.r s.1 s.2.1 s.2.2 ^ p * S.ρ.r t.1 t.2.1 t.2.2 ^ q ∈ S.ρ.mon 0 :=
      ⟨List.replicate p s ++ List.replicate q t, by simpa using h, by simp⟩
    exact ⟨⟨_, S.mon_mem hm⟩, rfl⟩
end

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def sg (K : Type) [CommRing K] (j : ZMod 2) : K := (-1) ^ j.val

def pw (a b : Fin 3) : ZMod 2 := ((w 3 a - w 3 b : ℤ) : ZMod 2)

def adp (K : Type) [CommRing K] (j : ZMod 2) : Submodule K (Matrix (Fin 3) (Fin 3) K) where
  carrier := {X | ∀ a b, pw a b ≠ j → X a b = 0}
  add_mem' h h' a b e := by simp [h a b e, h' a b e]
  zero_mem' _ _ _ := rfl
  smul_mem' c X h a b e := by simp [h a b e]

def prp (K : Type) [CommRing K] (j : ZMod 2) : Matrix (Fin 3) (Fin 3) K →ₗ[K] adp K j where
  toFun X := ⟨Matrix.of fun a b => if pw a b = j then X a b else 0, fun a b e => by simp [e]⟩
  map_add' X Y := Subtype.ext (by ext a b; by_cases e : pw a b = j <;> simp [e])
  map_smul' c X := Subtype.ext (by ext a b; by_cases e : pw a b = j <;> simp [e])

def evp {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) : Submodule O R where
  carrier := {x | σ x = sg R j * x}
  add_mem' {x y} (h : _ = _) (h' : _ = _) := show _ = _ by rw [map_add (f := _), h, h', mul_add]
  zero_mem' := show _ = _ by simp
  smul_mem' c x (h : _ = _) := show _ = _ by rw [map_smul, h, mul_smul_comm]

section Pres

variable (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R)

def derp (j : ZMod 2) : Submodule (ResidueField O) (R →ₗ[O] ResidueField O) :=
  PtDer (res O R) (ResidueField O) ⊓
    { carrier := {D | ∀ x, D (σ x) = sg (ResidueField O) j * D x}
      add_mem' := fun h h' x => by simp only [LinearMap.add_apply, h x, h' x, mul_add]
      zero_mem' := fun x => by simp
      smul_mem' := fun c D h x => by simp only [LinearMap.smul_apply, h x, smul_eq_mul, mul_left_comm] }

structure GPres where
  a : ℕ
  g : ℕ
  p : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R
  κ : Type
  [fin : Fintype κ]
  f : κ → MvPowerSeries (Fin a ⊕ Fin g) O
  wf : κ → ZMod 2
  surj : Function.Surjective p
  var : ∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal R
  part : ∀ j, (wtPart O (Space.Loc.par a g) j).map p.toLinearMap = evp σ j
  homog : IsHomog O (Space.Loc.par a g) (RingHom.ker p)
  min : ∀ h ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) h ∈ maximalIdeal O
  hf : ∀ u, f u ∈ wtPart O (Space.Loc.par a g) (wf u)
  ker : RingHom.ker p = Ideal.span (Set.range f)
  indep : ∀ c : κ → O, ∑ u, c u • f u ∈ maximalIdeal (MvPowerSeries (Fin a ⊕ Fin g) O) * RingHom.ker p →
    ∀ u, c u ∈ maximalIdeal O

attribute [instance] GPres.fin

end Pres

structure Space.Loc.IsInv {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {F : Frame l (ResidueField O)} {S : Space O F 3} {x : Ideal S.A} (L : S.Loc x) (σ : L.R →ₐ[L.O'] L.R) : Prop where
  sq : ∀ y, σ (σ y) = y
  ent : ∀ g a b, L.ρ.r g a b ∈ evp σ (pw a b)
  base : ∀ y : S.B, L.b y ∈ evp σ 0

end UpperTheory.V.Fr
end
end
