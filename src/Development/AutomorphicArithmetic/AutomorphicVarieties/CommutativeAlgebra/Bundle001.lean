module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingUp
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

noncomputable section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun {f} hf => ?_⟩
  have hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (f := fun n => f n i) ?_
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [mem_smul_top_pi] at h
    have := h i
    simpa [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top] using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := hL i n
  rw [SModEq.sub_mem] at this
  simpa [smul_eq_mul, Ideal.mul_top] using this

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, φ, hφ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  have himg : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) = Submodule.map φ (I ^ n • ⊤) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hφ]
  refine ⟨fun {f} hf => ?_⟩
  have hmem : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := by
    intro n
    have := SModEq.sub_mem.1 (hf (Nat.le_succ n))
    rw [← neg_sub]
    exact neg_mem this
  have hd : ∀ n, ∃ d : Fin r → R, d ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)) ∧ φ d = f (n + 1) - f n := by
    intro n
    have := hmem n
    rw [himg n, Submodule.mem_map] at this
    exact this
  choose d hdmem hdφ using hd
  obtain ⟨y0, hy0⟩ := hφ (f 0)
  set g : ℕ → (Fin r → R) := fun n => y0 + ∑ k ∈ Finset.range n, d k with hg
  have hgφ : ∀ n, φ (g n) = f n := by
    intro n
    induction n with
    | zero => simp [hg, hy0]
    | succ n ih =>
      have : g (n + 1) = g n + d n := by
        simp only [hg, Finset.sum_range_succ]; abel
      rw [this, map_add (f := _), ih, hdφ]; abel
  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have : g m - g n = -∑ k ∈ Finset.Ico m n, d k := by
      rw [Finset.sum_Ico_eq_sub _ hmn]; simp only [hg]; abel
    rw [this]
    refine neg_mem (Submodule.sum_mem _ fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1) (hdmem k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' g hgc
  refine ⟨φ L, fun n => ?_⟩
  have h1 := (hL n).map φ
  rw [hgφ, ← himg n] at h1
  exact h1

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := by
  have hsm : ∀ (K : Ideal R) (x : R), x ∈ (K • (⊤ : Submodule R R)) ↔ x ∈ K := by
    intro K x
    simp [smul_eq_mul, Ideal.mul_top]
  have he' : I ^ (e + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ e)) he
  have hpow : ∀ k, I ^ ((e + 1) * k) ≤ J ^ k := by
    intro k
    rw [pow_mul]
    exact Ideal.pow_right_mono he' k
  refine ⟨fun {f} hf => ?_⟩
  have hgc : ∀ {m n : ℕ}, m ≤ n →
      f ((e + 1) * m) ≡ f ((e + 1) * n) [SMOD (J ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
    rw [SModEq.sub_mem, hsm] at h ⊢
    exact hpow m h
  obtain ⟨L, hL⟩ := hJ.prec' (fun k => f ((e + 1) * k)) hgc
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (show n ≤ (e + 1) * n by nlinarith)
  have h2 := hL n
  rw [SModEq.sub_mem, hsm] at h1 h2 ⊢
  have h3 : f ((e + 1) * n) - L ∈ I ^ n := Ideal.pow_right_mono hJI n h2
  have := Ideal.add_mem _ h1 h3
  simpa using this

theorem UpperTheory.V.Alg.co_finite :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'] [IsLocalRing R'],
      (∀ x : R', ∃ a : O, x - algebraMap O R' a ∈ maximalIdeal R') → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ _ _ _ hres
  haveI : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)
  haveI : IsNoetherian R R' := inferInstance
  haveI hN : IsNoetherianRing R' := isNoetherian_of_tower R this
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI hcompl : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hcomap : ∀ P : Ideal R', P.IsPrime → maximalIdeal R ≤ P.comap (algebraMap R R') → P = maximalIdeal R' := by
    intro P hP hle
    have hcm : (P.comap (algebraMap R R')).IsMaximal := by
      have hne : P.comap (algebraMap R R') ≠ ⊤ := (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      have : P.comap (algebraMap R R') = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hne) hle
      rw [this]; infer_instance
    haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R')
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P hcm
    exact IsLocalRing.eq_maximalIdeal this
  have hcm' : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R'))
  have hloc : IsLocalHom (algebraMap R R') := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
    rw [← hcm', Ideal.mem_comap] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this ha
  set J : Ideal R' := (maximalIdeal R).map (algebraMap R R') with hJdef
  have hJI : J ≤ maximalIdeal R' := by
    rw [hJdef, Ideal.map_le_iff_le_comap, hcm']
  have hrad : maximalIdeal R' ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨hJP, hPp⟩ := hP
    rw [hcomap P hPp (Ideal.map_le_iff_le_comap.1 hJP)]
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal R) R' := isPrecomplete_finite (R := R) (M := R') (maximalIdeal R)
  have hJp : IsPrecomplete J R' := by
    rw [hJdef]
    exact IsPrecomplete.map_algebraMap_iff.2 this
  have hprec : IsPrecomplete (maximalIdeal R') R' := prec_cofinal hJI he hJp
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hlocO : IsLocalHom (algebraMap O R') := by
    rw [IsScalarTower.algebraMap_eq O R R']
    infer_instance
  exact
    { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hprec }
      isLocalHom := hlocO
      res_surj := hres }
end
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_fin_min {σ : Type} [Fintype σ] (P : (σ →₀ ℕ) → Prop) :
    ∃ T : Finset (σ →₀ ℕ), (∀ m ∈ T, P m) ∧ ∀ n, P n → ∃ m ∈ T, m ≤ n := by
  classical
  have hfin : {m : σ →₀ ℕ | Minimal P m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, ?_⟩
  intro n hn
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE {x | P x}).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

private theorem exists_decomp {O σ X : Type} [CommRing O] [Fintype σ] [AddCommGroup X] (wt : σ → X) (j : X)
    (f : MvPowerSeries σ O) (hf : f ∈ wtPart O wt j) :
    ∃ (T : Finset (σ →₀ ℕ)) (g : (σ →₀ ℕ) → MvPowerSeries σ O), (∀ m ∈ T, g m ∈ wtPart O wt 0) ∧
      f = ∑ m ∈ T, monomial m (1 : O) * g m := by
  classical
  obtain ⟨T, hTP, hT⟩ := exists_fin_min (fun n => coeff n f ≠ 0)
  choose! c hcT hcle using hT
  obtain ⟨g, hg⟩ : ∃ g : (σ →₀ ℕ) → MvPowerSeries σ O, ∀ m k,
      coeff k (g m) = if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0 :=
    ⟨fun m k => if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
  have hwt : ∀ n, coeff n f ≠ 0 → Finsupp.weight wt n = j := by
    intro n hn
    by_contra h
    exact hn (hf n h)
  refine ⟨T, g, ?_, ?_⟩
  · intro m hmT k hk
    rw [hg, if_neg]
    rintro ⟨h1, h2⟩
    apply hk
    have hm : Finsupp.weight wt m = j := hwt m (hTP m hmT)
    have hkm := hwt _ h1
    rw [map_add (f := _), hm] at hkm
    simpa using hkm
  · ext n

    rw [map_sum, Finset.sum_congr rfl
    (g := fun m => if c n = m then (if coeff n f ≠ 0 then coeff n f else 0) else 0),
    Finset.sum_ite_eq]
    · by_cases hn : coeff n f ≠ 0
      · rw [if_pos (hcT n hn), if_pos hn]
      · push_neg at hn
        rw [hn]
        simp
    · intro m _
      rw [MvPowerSeries.coeff_monomial_mul, one_mul]
      by_cases hmn : m ≤ n
      · rw [if_pos hmn, hg, tsub_add_cancel_of_le hmn]
        by_cases h1 : coeff n f ≠ 0 <;> by_cases h2 : c n = m <;> simp [h1, h2]
      · rw [if_neg hmn]
        by_cases h1 : coeff n f ≠ 0
        · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
          simp [h3]
        · push_neg at h1
          simp [h1]

private theorem monomial_eq_prod {O σ : Type} [CommRing O] [Fintype σ] (m : σ →₀ ℕ) :
    (monomial m (1 : O) : MvPowerSeries σ O) = ∏ i, (MvPowerSeries.X i) ^ (m i) := by
  classical
  have key : ∀ s : Finset σ, ∏ i ∈ s, (MvPowerSeries.X i : MvPowerSeries σ O) ^ (m i) =
      monomial (∑ i ∈ s, Finsupp.single i (m i)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [MvPowerSeries.monomial_zero_one]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [key, Finsupp.univ_sum_single]

theorem UpperTheory.V.Alg.gr_gen :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R), Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) = ⊤ := by
  intro O R _ _ _ X _ _ _ W
  classical
  haveI := W.fin
  rw [Algebra.eq_top_iff]
  rintro ⟨x, hx⟩
  refine Submodule.iSup_induction' (p := W.part)
    (motive := fun x h => (⟨x, h⟩ : W.A) ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA))
    ?_ ?_ ?_ hx
  · intro j y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨T, g, hg, hfe⟩ := exists_decomp W.wt j f hf
    have hg' : ∀ m, (if m ∈ T then g m else 0) ∈ wtPart O W.wt 0 := by
      intro m
      split_ifs with h
      · exact hg m h
      · exact zero_mem _
    let e : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (if m ∈ T then g m else 0), W.part_le_A (Submodule.mem_map_of_mem (hg' m))⟩
    have he : ∀ m, e m ∈ W.gr 0 := fun m => Submodule.mem_map_of_mem (hg' m)
    have hmem : (∑ m ∈ T, (∏ i, W.zA i ^ m i) * e m) ∈
        Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      refine Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ ?_ ?_
      · refine Subalgebra.prod_mem _ fun i _ => pow_mem ?_ _
        exact Algebra.subset_adjoin (Set.mem_union_right _ ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Set.mem_union_left _ (he m))
    convert hmem using 1
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, e, WPres.zA, WPres.z]

    rw [AlgHom.toLinearMap_apply, hfe, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos hm, map_mul, monomial_eq_prod, map_prod]
    simp only [map_pow]
  · exact Subalgebra.zero_mem _
  · intro x y _ _ ihx ihy
    exact Subalgebra.add_mem _ ihx ihy
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.part_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R) (S : Set (W.σ →₀ ℕ)) (j : X), (∀ n ∈ S, Finsupp.weight W.wt n = j) →
      ∃ μ : Finset (W.σ →₀ ℕ), (μ : Set _) ⊆ S ∧ ∀ f : MvPowerSeries W.σ O, (∀ n, n ∉ S → coeff n f = 0) →
        ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, (∀ m, b m ∈ wtPart O W.wt 0) ∧ f = ∑ m ∈ μ, b m * monomial m 1 := by
  intro O R _ _ _ X _ _ _ W S j hS
  classical
  haveI := W.fin
  have hMfin : {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  have hex : ∀ n ∈ S, ∃ m ∈ {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}, m ≤ n := by
    intro n hn
    obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
    exact ⟨b, hmin, hb⟩
  choose! c hcM hcle using hex
  refine ⟨hMfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact fun m hm => hm.1
  · intro f hf
    obtain ⟨b, hb⟩ : ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, ∀ m k,
        coeff k (b m) = if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0 :=
      ⟨fun m k => if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
    refine ⟨b, ?_, ?_⟩
    · intro m k hk
      rw [hb, if_neg]
      rintro ⟨h1, h2⟩
      apply hk
      have hm : Finsupp.weight W.wt m = j := hS m (by rw [← h2]; exact (hcM _ h1).1)
      have hkm := hS _ h1
      rw [map_add (f := _), hm] at hkm
      simpa using hkm
    · ext n

      rw [map_sum, Finset.sum_congr rfl
      (g := fun m => if c n = m then (if n ∈ S then coeff n f else 0) else 0), Finset.sum_ite_eq]
      · by_cases hn : n ∈ S
        · rw [if_pos ((Set.Finite.mem_toFinset hMfin).2 (hcM n hn)), if_pos hn]
        · rw [hf n hn]
          simp
      · intro m _
        rw [MvPowerSeries.coeff_mul_monomial, mul_one]
        by_cases hmn : m ≤ n
        · rw [if_pos hmn, hb, tsub_add_cancel_of_le hmn]
          by_cases h1 : n ∈ S <;> by_cases h2 : c n = m <;> simp [h1, h2]
        · rw [if_neg hmn]
          by_cases h1 : n ∈ S
          · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
            simp [h3]
          · simp [h1]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem prec_of_surj {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R')
    (hp : Function.Surjective p) (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete (I.map p) R' := ⟨fun f hf => by
  have hd : ∀ n, ∃ d ∈ I ^ n, p d = f (n + 1) - f n := fun n => by
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] at h
    exact (Ideal.mem_map_iff_of_surjective p hp).1 h
  choose d hdI hd using hd
  obtain ⟨x, hx⟩ := hp (f 0)
  have hg : ∀ n, p (x + ∑ i ∈ Finset.range n, d i) = f n := fun n => by
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, map_add (f := _), ih, hd]; ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => x + ∑ i ∈ Finset.range n, d i) (fun {m n} hmn => by
    apply SModEq.symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, add_sub_add_left_eq_sub, ← Finset.sum_Ico_eq_sub _ hmn]
    exact Ideal.sum_mem _ fun i hi => Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hdI i))
  refine ⟨p L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h ⊢
  rw [← hg n, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem p h⟩

theorem UpperTheory.V.Alg.co_quot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Nontrivial R'] (p : R →ₐ[O] R'), Function.Surjective p → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ p hp
  have hp' : Function.Surjective (p : R →+* R') := hp
  haveI hL : IsLocalRing R' := IsLocalRing.of_surjective' (p : R →+* R') hp'
  haveI hN : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (p : R →+* R') hp'
  haveI hH : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp'
  have hm : (maximalIdeal R).map (p : R →+* R') = maximalIdeal R' :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hp'
  have hP : IsPrecomplete (maximalIdeal R') R' := hm ▸ prec_of_surj (p : R →+* R') hp' (maximalIdeal R)
  refine { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
           isLocalHom := ⟨fun a ha => ?_⟩
           res_surj := fun y => ?_ }
  · rw [← p.commutes] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap O R) a (IsLocalHom.map_nonunit (f := (p : R →+* R')) _ ha)
  · obtain ⟨x, rfl⟩ := hp y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨a, ?_⟩
    rw [← p.commutes, ← map_sub, ← hm]
    exact Ideal.mem_map_of_mem _ ha
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_surj :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), maximalIdeal R' ≤ (maximalIdeal R).map f ⊔ maximalIdeal R' ^ 2 → Function.Surjective f := by
  intro O _ _ R _ _ _ R' _ _ _ f hf
  have hle : (maximalIdeal R).map f ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O R', res_map, res_eq_zero_iff]
    exact hx
  have heq : (maximalIdeal R).map (f : R →+* R') = maximalIdeal R' := by
    refine le_antisymm hle ?_
    have hfg : (maximalIdeal R').FG := IsNoetherian.noetherian _
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson _) ?_
    rw [smul_eq_mul, ← pow_two]
    exact hf
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := O)
  haveI : IsHausdorff ((maximalIdeal R).map (f : R →+* R')) R' := by
    rw [heq]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal R) (f : R →+* R')
  intro y
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y0
  refine ⟨algebraMap O R a, ?_⟩
  show Ideal.Quotient.mk _ ((f : R →+* R') (algebraMap O R a)) = Ideal.Quotient.mk _ y0
  rw [Ideal.Quotient.eq, heq, AlgHom.coe_toRingHom, AlgHom.commutes, ← neg_sub]
  exact neg_mem ha
end
