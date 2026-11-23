module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle005
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frobenius_corner_units :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F 3 K), Cone O C ρ → CornerUnits ρ := by
  intro l _ O _ _ _ _ F C₀ hF C _ _ _ K _ _ ρ hC v
  obtain ⟨g, hg⟩ := hF.f3 v
  obtain ⟨χ, hχ, hχρ⟩ := hC.psi
  have key : ∀ a : C, res O C a ≠ 0 → IsUnit (algebraMap C K a) := by
    intro a ha
    apply IsUnit.map
    by_contra hu
    exact ha ((res_eq_zero_iff O C a).mpr ((IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hu)))
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have hg' : F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) ^ 2 ≠ 1 := hg
  have hu1 : ((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) : (ResidueField O)ˣ) : ResidueField O) ≠ 1 := by
    intro h
    apply hg'
    ext
    rw [Units.val_pow_eq_pow_val, h, one_pow, Units.val_one]
  have hu2 : (((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ))⁻¹ : (ResidueField O)ˣ) : ResidueField O) ≠ 1 := by
    intro h
    apply hg'
    have h1 : F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) = 1 := inv_eq_one.mp (Units.ext (by rw [h, Units.val_one]))
    rw [h1, one_pow]
  obtain ⟨c0, hc0, hr0⟩ := hC.dg (F.loc0 v g) 0
  obtain ⟨c1, hc1, hr1⟩ := hC.dg (F.loc0 v g) 1
  obtain ⟨c2, hc2, hr2⟩ := hC.dg (F.loc0 v g) 2
  rw [w0, zpow_one] at hr0
  rw [w1, zpow_zero, Units.val_one] at hr1
  rw [w2, _root_.zpow_neg_one] at hr2
  have x0 : res O C (χ v 0 g) = ((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) : (ResidueField O)ˣ) : ResidueField O) := by
    have h := (hχ v 0).2 g
    rw [w0, zpow_one] at h
    exact h
  have x1 : res O C (χ v 1 g) = 1 := by
    have h := (hχ v 1).2 g
    rw [w1, zpow_zero, Units.val_one] at h
    exact h
  have x2 : res O C (χ v 2 g) = (((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ))⁻¹ : (ResidueField O)ˣ) : ResidueField O) := by
    have h := (hχ v 2).2 g
    rw [w2, _root_.zpow_neg_one] at h
    exact h
  have h02 : ((0 : Fin 3) : Fin 3) ≠ 2 := by decide
  obtain ⟨m, hm, hme⟩ := hC.cyc [(F.loc0 v g, 0, 2), (F.loc0 v g, 2, 0)] (by simp [w])
    ⟨(F.loc0 v g, 0, 2), by simp, h02⟩
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hme
  refine ⟨g, ?_, ?_, ?_⟩
  · have hk := key (c1 - χ v 0 g) ?_
    · rwa [map_sub, hc1, hχρ] at hk
    · rw [map_sub, hr1, x0]
      exact sub_ne_zero.mpr (Ne.symm hu1)
  · have hk := key (c1 - χ v 2 g) ?_
    · rwa [map_sub, hc1, hχρ] at hk
    · rw [map_sub, hr1, x2]
      exact sub_ne_zero.mpr (Ne.symm hu2)
  · have hk := key ((c0 - χ v 1 g) * (c2 - χ v 1 g) - m) ?_
    · rwa [map_sub, map_mul, map_sub, map_sub, hc0, hc2, hχρ, hme] at hk
    · rw [map_sub, map_mul, map_sub, map_sub, hr0, hr2, x1, (res_eq_zero_iff O C m).mpr hm, sub_zero]
      exact mul_ne_zero (sub_ne_zero.mpr hu1) (sub_ne_zero.mpr hu2)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem locConst_of_factor {X Y Z : Type} [TopologicalSpace X] {f : X → Y} (hf : IsLocallyConstant f)
    (h : X → Z) (H : ∀ x y, f x = f y → h x = h y) : IsLocallyConstant h := by
  intro s
  have e : h ⁻¹' s = f ⁻¹' (f '' (h ⁻¹' s)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      show h x ∈ s
      rw [← H y x hyx]
      exact hy
  rw [e]
  exact hf _

private theorem algebraMap_mem_vertex_pow {C K : Type} [CommRing C] [CommRing K] [Algebra C K] [IsLocalRing C]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) {c : C}
    (hc : c ∈ maximalIdeal C ^ N) : algebraMap C (lauSub P) c ∈ vertex (P := P) h ^ N := by
  have hle : Ideal.map (algebraMap C (lauSub P)) (maximalIdeal C) ≤ vertex (P := P) h := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap]
    change ∃ a ∈ maximalIdeal C,
      algebraMap C K a = ((algebraMap C (lauSub P) c : lauSub P).1).coeff 0
    refine ⟨c, hc, ?_⟩
    show _ = (AddMonoidAlgebra.single 0 (algebraMap C K c)).coeff 0
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have hm := Ideal.mem_map_of_mem (algebraMap C (lauSub P)) hc
  rw [Ideal.map_pow] at hm
  exact Ideal.pow_right_mono hle N hm

private theorem single_mem_vertex_pow {C K : Type} [CommRing C] [CommRing K] [Algebra C K] [IsLocalRing C]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) (d : ℤ) (M : Submodule C K)
    (hM : M ≤ P d) {x : K} (hx : x ∈ maximalIdeal C ^ N • M) :
    ∃ p ∈ vertex (P := P) h ^ N, (p : lauSub P).1 = AddMonoidAlgebra.single d x := by
  refine Submodule.smul_induction_on
    (p := fun y => ∃ p ∈ vertex (P := P) h ^ N, (p : lauSub P).1 = AddMonoidAlgebra.single d y) hx ?_ ?_
  · intro c hc m hm
    refine ⟨algebraMap C (lauSub P) c * ⟨AddMonoidAlgebra.single d m, single_mem_lauSub P (hM hm)⟩,
      Ideal.mul_mem_right _ _ (algebraMap_mem_vertex_pow h N hc), ?_⟩
    rw [Subalgebra.coe_mul]
    show AddMonoidAlgebra.single 0 (algebraMap C K c) * AddMonoidAlgebra.single d m = _
    rw [AddMonoidAlgebra.single_mul_single, zero_add, Algebra.smul_def]
  · rintro x y ⟨p, hp, hpx⟩ ⟨q, hq, hqy⟩
    exact ⟨p + q, add_mem hp hq, by rw [Subalgebra.coe_add, hpx, hqy, AddMonoidAlgebra.single_add]⟩

theorem UpperTheory.V.Fr.alg_cont :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∀ (h : HasVertex (ρ.part C)) (ρD : NRep F n (lauSub (ρ.part C))), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) → (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) → ρD.Cont (vertex (P := ρ.part C) h) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc h ρD hr hψ
  refine ⟨fun i j N => ?_, fun v i N => ?_⟩
  · refine locConst_of_factor (hc.cont i j N) _ fun g g' hgg => ?_
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hgg
    have hS : Submodule.span C (Set.range fun g => ρ.r g i j) ≤ ρ.part C (w n i - w n j) := by
      rw [Submodule.span_le]
      rintro _ ⟨g0, rfl⟩
      exact NRep.r_mem_part C ρ g0 i j
    obtain ⟨p, hp, hpe⟩ := single_mem_vertex_pow h N (w n i - w n j) _ hS hgg
    rw [Ideal.Quotient.eq]
    have e : ρD.r g i j - ρD.r g' i j = p := by
      apply Subtype.ext
      rw [hpe, AddSubgroupClass.coe_sub, hr, hr, AddMonoidAlgebra.single_sub]
    rw [e]
    exact hp
  · obtain ⟨χ, hχ, hχe⟩ := hc.psi
    refine locConst_of_factor ((hχ v i).1 N) _ fun g g' hgg => ?_
    rw [Ideal.Quotient.eq] at hgg ⊢
    have hm := algebraMap_mem_vertex_pow h N hgg
    have e : (↑(ρD.ψ v i g) : lauSub (ρ.part C)) - ↑(ρD.ψ v i g') =
        algebraMap C (lauSub (ρ.part C)) (χ v i g - χ v i g') := by
      apply Subtype.ext
      rw [AddSubgroupClass.coe_sub, hψ, hψ]
      show _ = AddMonoidAlgebra.single 0 (algebraMap C K (χ v i g - χ v i g'))
      rw [map_sub, hχe, hχe, AddMonoidAlgebra.single_sub]
    rw [e]
    exact hm
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_vertex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → HasVertex (ρ.part C) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hC
  have off : ∀ (L : List (F.G0 × Fin n × Fin n)) (j : ℤ),
      (L.map (fun s => w n s.2.1 - w n s.2.2)).sum = j → j ≠ 0 → ∃ s ∈ L, s.2.1 ≠ s.2.2 := by
    intro L j hL hj
    by_contra h
    push_neg at h
    apply hj
    rw [← hL]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    rw [h s hs, sub_self]
  constructor
  · intro x hx
    have hle : ρ.mon 0 ⊆ (LinearMap.range (Algebra.linearMap C K) : Set K) := by
      rintro _ ⟨L, hL, rfl⟩
      by_cases hd : ∃ s ∈ L, s.2.1 ≠ s.2.2
      · obtain ⟨c, -, hc⟩ := hC.cyc L hL hd
        exact ⟨c, hc⟩
      · push_neg at hd
        have hm : (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod ∈ (algebraMap C K).rangeS := by
          apply list_prod_mem
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
          rw [← hd s hs]
          obtain ⟨c, hc, -⟩ := hC.dg s.1 s.2.1
          exact ⟨c, hc⟩
        obtain ⟨c, hc⟩ := hm
        exact ⟨c, hc⟩
    obtain ⟨c, hc⟩ := Submodule.span_le.2 hle hx
    exact ⟨c, hc⟩
  · intro j hj x hx y hy
    open Pointwise in
    have hle : ρ.mon j * ρ.mon (-j) ⊆
        (Submodule.map (Algebra.linearMap C K) (maximalIdeal C) : Set K) := by
      rintro _ ⟨a, ⟨L1, h1, rfl⟩, b, ⟨L2, h2, rfl⟩, rfl⟩
      obtain ⟨s, hs, hne⟩ := off L1 j h1 hj
      obtain ⟨c, hc, hc'⟩ := hC.cyc (L1 ++ L2)
        (by rw [List.map_append, List.sum_append, h1, h2]; ring) ⟨s, List.mem_append_left _ hs, hne⟩
      refine Submodule.mem_map.2 ⟨c, hc, ?_⟩
      rw [Algebra.linearMap_apply, hc', List.map_append, List.prod_append]
    open Pointwise in
    have hxy : x * y ∈ Submodule.span C (ρ.mon j * ρ.mon (-j)) := by
      rw [← Submodule.span_mul_span]
      exact Submodule.mul_mem_mul hx hy
    obtain ⟨c, hc, hc'⟩ := Submodule.mem_map.1 (Submodule.span_le.2 hle hxy)
    exact ⟨c, hc, hc'⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frobenius_corner_mem_cone :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F 3 K) (σ : NRep F 2 K), IsCorner ρ σ → Cone O C ρ → Cone O C σ := by
  intro l _ O _ _ F C _ _ _ K _ _ ρ σ hc hC
  have cinj : Function.Injective cor := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [cor]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g i
    obtain ⟨c, h1, h2⟩ := hC.dg g (cor i)
    exact ⟨c, by rw [h1, hc.r], by rw [h2, w_cor]⟩
  · intro L hs hne
    have hs' : (List.map (fun s => w 3 s.2.1 - w 3 s.2.2) (L.map fun s => (s.1, cor s.2.1, cor s.2.2))).sum = 0 := by
      rw [← hs, List.map_map]
      congr 1
      apply List.map_congr_left
      intro s _
      simp [w_cor]
    have hne' : ∃ s ∈ L.map (fun s => (s.1, cor s.2.1, cor s.2.2)), s.2.1 ≠ s.2.2 := by
      obtain ⟨s, hs1, hs2⟩ := hne
      exact ⟨(s.1, cor s.2.1, cor s.2.2), List.mem_map_of_mem hs1, fun h => hs2 (cinj h)⟩
    obtain ⟨c, hcm, he⟩ := hC.cyc _ hs' hne'
    refine ⟨c, hcm, ?_⟩
    rw [he, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s _
    simp [hc.r]
  · intro i j
    simp only [hc.r]
    exact hC.fg _ _
  · intro i j N
    have e : (fun g => σ.r g i j) = fun g => ρ.r g (cor i) (cor j) := funext fun g => hc.r g i j
    have h := hC.cont (cor i) (cor j) N
    rw [← e] at h
    have e3 : (fun g => (maximalIdeal C ^ N • Submodule.span C (Set.range fun g => σ.r g i j)).mkQ (σ.r g i j)) =
        fun g => (maximalIdeal C ^ N • Submodule.span C (Set.range fun g => σ.r g i j)).mkQ (ρ.r g (cor i) (cor j)) :=
      funext fun g => by rw [hc.r]
    rw [e3]
    exact h
  · obtain ⟨χ, hχ, hχρ⟩ := hC.psi
    refine ⟨fun v i g => χ v (cor i) g, fun v i => ⟨(hχ v (cor i)).1, fun g => ?_⟩, fun v i g => ?_⟩
    · rw [(hχ v (cor i)).2 g, w_cor]
    · rw [hχρ, hc.ψ]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private noncomputable def UpperTheory.V.Fr.lauT (K : Type) [CommRing K] : Multiplicative ℤ →* (AddMonoidAlgebra K ℤ)ˣ :=
  (AddMonoidAlgebra.of K ℤ).toHomUnits

private theorem UpperTheory.V.Fr.lauT_zpow (K : Type) [CommRing K] (m : ℤ) :
    ((lauT K (Multiplicative.ofAdd 1) ^ m : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) =
      AddMonoidAlgebra.single m 1 := by
  rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  rfl

theorem UpperTheory.V.Fr.alg_lau :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∃ ρD : NRep F n (lauSub (ρ.part C)), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) ∧ (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc
  obtain ⟨χ, -, hχ⟩ := hc.psi
  obtain ⟨ρ', hr, hψ⟩ := alg_twist (lauT K (Multiplicative.ofAdd 1))
    (NRep.map (AddMonoidAlgebra.singleZeroRingHom : K →+* AddMonoidAlgebra K ℤ) ρ)
  have hr' : ∀ g i j, ρ'.r g i j = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) := by
    intro g i j
    rw [hr, lauT_zpow, NRep.map_r]
    simp [AddMonoidAlgebra.single_mul_single]
  have hψ' : ∀ v i g, ((ρ'.ψ v i g : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) =
      AddMonoidAlgebra.single 0 (ρ.ψ v i g : K) := by
    intro v i g
    rw [hψ]
    rfl
  have h1 : ∀ g i j, ρ'.r g i j ∈ lauSub (ρ.part C) := by
    intro g i j
    rw [hr']
    exact single_mem_lauSub _ (NRep.r_mem_part C ρ g i j)
  have h2 : ∀ v i g, ((ρ'.ψ v i g : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) ∈
      lauSub (ρ.part C) := by
    intro v i g
    rw [hψ']
    apply single_mem_lauSub
    rw [← hχ, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  exact ⟨NRep.restrict ρ' (lauSub (ρ.part C)) h1 h2, fun g i j => hr' g i j,
    fun v i g => hψ' v i g⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem rank_tr {k K G V : Type} [Field k] [Field K] (f : k →+* K) [Group G] [TopologicalSpace G]
    [CompactSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (χ : G →* kˣ)
    (χ' : G →* Kˣ) (h : ∀ g, χ' g = Units.map f.toMonoidHom (χ g)) :
    Module.rank K (H1C loc (chRep χ') fun _ => ⊥) = Module.rank k (H1C loc (chRep χ) fun _ => ⊥) ∧
    Module.rank K (H1C loc (chRep χ') fun _ => ⊤) = Module.rank k (H1C loc (chRep χ) fun _ => ⊤) := by
  have hχ : χ' = (Units.map (f : k →* K)).comp χ := MonoidHom.ext fun g => h g
  subst hχ
  exact ⟨(n4ch f loc χ (fun _ => ⊥) (fun _ => ⊥) (fun _ => Or.inl ⟨rfl, rfl⟩)).2,
    (n4ch f loc χ (fun _ => ⊤) (fun _ => ⊤) (fun _ => Or.inr ⟨rfl, rfl⟩)).2⟩

private theorem nontriv_tr {k K M N : Type} [Field k] [Field K] [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module K N] (e : Module.rank K N = Module.rank k M) (h : Nontrivial M) : Nontrivial N := by
  rw [← rank_pos_iff_nontrivial (R := K), e]
  exact rank_pos_iff_nontrivial.2 h

theorem UpperTheory.V.Fr.ok_ext :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {k' : Type} [Field k'] [Finite k'] [CharP k' l] (f : k →+* k'), F.Ok C₀ → (F.ext f).Ok C₀ := by
  intro l _ k _ _ F C₀ k' _ _ _ f h
  have hinj : Function.Injective f := f.injective
  have hU : ∀ u v : kˣ, Units.map (f : k →* k') u = Units.map (f : k →* k') v → u = v := by
    intro u v huv
    ext
    apply hinj
    simpa using congrArg Units.val huv
  have hU1 : ∀ u : kˣ, Units.map (f : k →* k') u = 1 → u = 1 := by
    intro u hu
    apply hU
    rw [hu, map_one]
  have hΨ : ∀ g, (F.ext f).Ψ g = Units.map (f : k →* k') (F.Ψ g) := fun g => rfl
  have hz : ∀ x : ZMod l, f (ZMod.castHom (dvd_refl l) k x) = ZMod.castHom (dvd_refl l) k' x :=
    fun x => RingHom.congr_fun
      (Subsingleton.elim (f.comp (ZMod.castHom (dvd_refl l) k)) (ZMod.castHom (dvd_refl l) k')) x
  have hom : ∀ g, (F.ext f).om k' g = Units.map (f : k →* k') (F.om k g) := by
    intro g
    ext
    change ((ZMod.castHom (dvd_refl l) k').comp PadicInt.toZMod) ((F.eps g : ℤ_[l])) =
      f (((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) ((F.eps g : ℤ_[l])))
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact (hz _).symm
  have hdel : ∀ g, (F.ext f).delK k' g = Units.map (f : k →* k') (F.delK k g) := by
    intro g
    ext
    change (Int.castRingHom k') (F.del g : ℤ) = f ((Int.castRingHom k) (F.del g : ℤ))
    simp
  have hker : (F.ext f).Ψ.ker = F.Ψ.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    exact ⟨hU1 _, fun h1 => by rw [hΨ, h1, map_one]⟩
  haveI : CompactSpace F.G0 :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ h.del_open).isCompact
  have hχ1 : ∀ g : F.Γ, ((F.ext f).Ψ⁻¹ * (F.ext f).delK k') g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹ * F.delK k) g) := by
    intro g
    change ((F.ext f).Ψ g)⁻¹ * (F.ext f).delK k' g = Units.map f.toMonoidHom ((F.Ψ g)⁻¹ * F.delK k g)
    erw [hdel, hΨ, map_mul, map_inv]
    rfl
  have hχ2 : ∀ g : F.Γ, ((F.ext f).Ψ⁻¹ ^ 2 * (F.ext f).delK k') g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹ ^ 2 * F.delK k) g) := by
    intro g
    rw [pow_two, pow_two]
    change ((F.ext f).Ψ g)⁻¹ * ((F.ext f).Ψ g)⁻¹ * (F.ext f).delK k' g =
      Units.map f.toMonoidHom ((F.Ψ g)⁻¹ * (F.Ψ g)⁻¹ * F.delK k g)
    erw [hdel, hΨ, map_mul, map_mul, map_inv]
    rfl
  have hχ3 : ∀ g : F.G0, ((F.ext f).Ψ⁻¹.comp (F.ext f).del.ker.subtype) g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹.comp F.del.ker.subtype) g) := by
    intro g
    change (Units.map (f : k →* k') (F.Ψ (g : F.Γ)))⁻¹ = Units.map f.toMonoidHom ((F.Ψ (g : F.Γ))⁻¹)
    rw [map_inv]
    rfl
  have hχ4 : ∀ g : F.Γ, (1 : F.Γ →* k'ˣ) g = Units.map f.toMonoidHom ((1 : F.Γ →* kˣ) g) := by
    intro g
    rw [MonoidHom.one_apply, MonoidHom.one_apply, map_one]
  exact
    { l_odd := h.l_odd
      fin := inferInstance
      del_open := h.del_open
      c_sq := h.c_sq
      del_c := h.del_c
      loc_cont := h.loc_cont
      eps_cont := h.eps_cont
      Ψ_open := by rw [hker]; exact h.Ψ_open
      Ψ_c := by
        show Units.map (f : k →* k') (F.Ψ F.c) = 1
        rw [h.Ψ_c, map_one]
      baseSubgroup_spec := fun he => h.baseSubgroup_spec (hU1 _ (by rw [map_pow]; exact he))
      phi := h.phi
      card_inf := h.card_inf
      cw_sq := h.cw_sq
      del_cw := h.del_cw
      f2a := by
        obtain ⟨g, hg⟩ := h.f2a
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        rw [hom] at he
        exact he
      f2b := by
        intro j hj
        obtain ⟨g, hg⟩ := h.f2b j hj
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        rw [hom, hΨ] at he
        rw [map_mul, map_zpow]
        exact he
      f2c := by
        intro j hj
        obtain ⟨g, hg⟩ := h.f2c j hj
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        erw [hom, hdel] at he
        rw [map_mul, map_mul, map_zpow]
        exact he
      f3 := by
        intro v
        obtain ⟨g, hg⟩ := h.f3 v
        exact ⟨g, fun he => hg (hU1 _ (by rw [map_pow]; exact he))⟩
      f4 := nontriv_tr (rank_tr f F.loc _ _ hχ1).1 h.f4
      f4' := nontriv_tr (rank_tr f F.loc _ _ hχ2).1 h.f4'
      f5 := by
        rintro ⟨j, hj⟩
        refine h.f5 ⟨j, fun g => hU _ _ ?_⟩
        have hg := hj g
        rw [hom, hΨ] at hg
        rw [map_zpow]
        exact hg
      Ψ_N := fun v g hg => by
        show Units.map (f : k →* k') (F.Ψ (F.loc v g)) = 1
        rw [h.Ψ_N v g hg, map_one]
      gen := by
        intro v
        obtain ⟨u, a₀, h1, h2, h3⟩ := h.gen v
        refine ⟨u, a₀, fun a => ⟨(h1 a).1, ?_⟩, h2, h3⟩
        show Units.map (f : k →* k') (F.Ψ (F.loc v (u a))) = 1
        rw [(h1 a).2, map_one]
      cl := h.cl
      ec := h.ec
      b1p := (rank_tr f F.loc _ _ hχ2).1.trans_le h.b1p
      b1 := (rank_tr f F.loc2 _ _ hχ3).1.trans_le h.b1
      h1 := (rank_tr f F.loc _ _ hχ4).2.trans_le h.h1 }
end
