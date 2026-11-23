module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresEx
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem lb_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have h1 : IsUnit ((t : O) - 1) := by
    have : (t : O) ^ 2 - 1 = ((t : O) - 1) * ((t : O) + 1) := by ring
    rw [this] at ht
    exact isUnit_of_mul_isUnit_left ht
  have hi : ((t⁻¹ : Oˣ) : O) * (t : O) = 1 := by simp
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have : (t : O) - ((t⁻¹ : Oˣ) : O) = ((t⁻¹ : Oˣ) : O) * ((t : O) ^ 2 - 1) := by
      linear_combination (-(t : O)) * hi
    rw [this]
    exact (Units.isUnit _).mul ht
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have : 1 - ((t⁻¹ : Oˣ) : O) = ((t⁻¹ : Oˣ) : O) * ((t : O) - 1) := by
      linear_combination (-1 : O) * hi
    rw [this]
    exact (Units.isUnit _).mul h1
  fin_cases a <;> fin_cases b <;> simp [wt1] at hab ⊢
  all_goals first
    | exact h1 | exact h2 | exact h3
    | exact (by simpa [neg_sub] using h1.neg)
    | exact (by simpa [neg_sub] using h2.neg)
    | exact (by simpa [neg_sub] using h3.neg)

theorem UpperTheory.V.UnitaryThreeInertia.lt_basis :
    ∀ {O R R' D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] [IsCO O R'] [Group D]
      (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R'), Function.Surjective p →
      ∀ (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r' : D →* GG (m := 3) (R := R')) (x : D), Red η Ψ r' → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → CondT η Ψ I r' →
      (∃ X, GrMat 𝒜 X ∧ X.map p = (r' x).mat) →
      ∃ h : GL (Fin 3) R, InHat h ∧ GrMat 𝒜 h.val ∧ InHat (GeneralLinearGroup.map (p : R →+* R') h) ∧ TriIn η Ψ I r' (GeneralLinearGroup.map (p : R →+* R') h) := by
  intro O R R' D _ _ _ _ _ _ _ _ _ _ 𝒜 _ p hp η Ψ I r' x hr hx hΨ hc hex
  obtain ⟨X, hX, hXp⟩ := hex
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  haveI : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  have hm : ∀ y : R, p y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
    intro y
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff (p : R →+* R') y)
  have hd : (r0 η Ψ x).mat = diagonal fun i => (((Ψ x) ^ wt1 i : Oˣ) : O) := by
    unfold GG.mat
    rw [unitaryThreeReflection_left, tor_val]
  have hred := hr.red x
  rw [hd] at hred
  have hent : ∀ a b : Fin 3, p (X a b) = (r' x).mat a b := by
    intro a b
    rw [← hXp]
    rfl
  have hoff : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R := by
    intro a b hab
    rw [← hm, hent]
    have := hred a b
    simpa [Matrix.map_apply, Matrix.diagonal_apply_ne _ hab] using this
  have hdiff : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b) := by
    intro a b hab
    by_contra hn
    have h1 : X a a - X b b ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    rw [← hm, map_sub, hent, hent] at h1
    have ha := hred a a
    have hb := hred b b
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply_eq] at ha hb
    have hu : IsUnit (algebraMap O R' ((((Ψ x) ^ wt1 a : Oˣ) : O) - (((Ψ x) ^ wt1 b : Oˣ) : O))) :=
      (lb_unit (Ψ x) hΨ a b hab).map _
    apply (IsLocalRing.mem_maximalIdeal _).mp _ hu
    have : algebraMap O R' ((((Ψ x) ^ wt1 a : Oˣ) : O) - (((Ψ x) ^ wt1 b : Oˣ) : O)) =
        ((r' x).mat a a - (r' x).mat b b) - ((r' x).mat a a - algebraMap O R' (((Ψ x) ^ wt1 a : Oˣ) : O))
          + ((r' x).mat b b - algebraMap O R' (((Ψ x) ^ wt1 b : Oˣ) : O)) := by
      rw [map_sub]
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.sub_mem _ h1 ha) hb
  obtain ⟨h, hh⟩ := exists_canon X hdiff hoff
  have hg := canon_graded 𝒜 X h hdiff hX hh
  have hh' := canon_map.1 (p : R →+* R') X h hh
  have hXp' : X.map (p : R →+* R') = (r' x).mat := hXp
  rw [hXp'] at hh'
  exact ⟨h, hh.hat, hg.1, hh'.hat, (cond_iff_canon η Ψ I r' x _ hr hx hΨ hh').1.1 hc⟩
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem wtPart_decomp {O σ : Type} [CommRing O] (wt : σ → ℤ) (j : ℤ) (s : Finset σ) :
    ∀ f ∈ wtPart O wt j, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0) →
      ∃ g : σ → MvPowerSeries σ O, (∀ i, g i ∈ wtPart O wt (j - wt i)) ∧
        f = ∑ i ∈ s, MvPowerSeries.X i * g i := by
  classical
  intro f hf hs
  let P : (σ →₀ ℕ) → σ → Prop := fun n i => ∃ h : ∃ k ∈ s, n k ≠ 0, h.choose = i
  let g : σ → MvPowerSeries σ O := fun i m =>
    if P (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ i m, MvPowerSeries.coeff m (g i) =
      if P (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 :=
    fun _ _ => rfl
  refine ⟨g, fun i m hm => ?_, ?_⟩
  · rw [hg]
    split_ifs
    · apply hf
      rw [map_add (f := _)]
      intro h
      apply hm
      have : (Finsupp.weight wt) (Finsupp.single i 1) = wt i := by
        rw [Finsupp.weight_apply, Finsupp.sum_single_index] <;> simp
      omega
    · rfl
  · have key : ∀ n i, MvPowerSeries.coeff n (MvPowerSeries.X i * g i) =
        if P n i then MvPowerSeries.coeff n f else 0 := by
      intro n i
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
      by_cases hle : Finsupp.single i 1 ≤ n
      · rw [if_pos hle, one_mul, hg, tsub_add_cancel_of_le hle]
      · have hP : ¬ P n i := by
          rintro ⟨h, hc⟩
          apply hle
          rw [Finsupp.single_le_iff, ← hc]
          exact Nat.one_le_iff_ne_zero.mpr h.choose_spec.2
        rw [if_neg hle, if_neg hP]
    ext n

    rw [map_sum]
    simp_rw [key]
    by_cases h : ∃ k ∈ s, n k ≠ 0
    · have hP : ∀ i, P n i ↔ h.choose = i := fun i => ⟨fun ⟨_, e⟩ => e, fun e => ⟨h, e⟩⟩
      simp_rw [hP]
      rw [Finset.sum_ite_eq, if_pos h.choose_spec.1]
    · have hP : ∀ i, ¬ P n i := fun i ⟨h', _⟩ => h h'
      simp only [hP, if_false, Finset.sum_const_zero]
      push_neg at h
      exact hs n h

private theorem vanish_of_entries {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : Frame O G Γ ι) {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG (m := 3) (R := R)) (W : WPres O ℤ R)
    (hW : F.Adapted u W) {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K) (M : AddSubmonoid ℤ)
    (h : ∀ g, F.η g = 1 → ∀ a b, wt a b ∉ M → ptMat u ξ g a b = 0) (j : ℤ) (hj : j ∉ M) (x : R)
    (hx : x ∈ wpart (O := O) u j) : ξ ⟨x, mem_Sring u hx⟩ = 0 := by
  classical
  haveI := W.fin
  have hmemz : ∀ i, W.z i ∈ Sring (O := O) u := fun i =>
    mem_Sring u (j := W.wt i) (by rw [← hW.part]; exact W.z_mem i)
  have hzero : ∀ i, W.wt i ∉ M → ξ ⟨W.z i, hmemz i⟩ = 0 := by
    intro i hi
    obtain ⟨g, a, b, hη, hw, hz⟩ := hW.var i
    have hab : a ≠ b := by
      rintro rfl
      apply hi
      rw [hw]
      simp [wt]
    have hrz : ((F.rz R) g).mat a b = 0 := by
      show algebraMap O R ((((tor O) (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0
      rw [tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
    have h1 : ξ ⟨W.z i, hmemz i⟩ = ptMat u ξ g a b := by
      show ξ ⟨W.z i, hmemz i⟩ = ξ ⟨(u g).mat a b, _⟩
      congr 1
      exact Subtype.ext (show W.z i = (u g).mat a b by rw [hz, hrz, sub_zero])
    rw [h1]
    exact h g hη a b (hw ▸ hi)
  rw [← hW.part] at hx
  obtain ⟨f, hf, hfx⟩ := hx
  subst hfx
  let s := Finset.univ.filter (fun i => W.wt i ∉ M)
  have hs : ∀ n : W.σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0 := by
    intro n hn
    apply hf
    intro hw
    apply hj
    rw [← hw, Finsupp.weight_apply]
    refine AddSubmonoid.sum_mem M fun c hc => ?_
    by_cases hcM : W.wt c ∈ M
    · exact nsmul_mem hcM _
    · exact absurd (hn c (by simp [s, hcM])) (Finsupp.mem_support_iff.mp hc)
  obtain ⟨g, hg, hfg⟩ := wtPart_decomp W.wt j s f hf hs
  have hmemg : ∀ i, W.π (g i) ∈ Sring (O := O) u := fun i =>
    mem_Sring u (j := j - W.wt i) (by rw [← hW.part]; exact ⟨g i, hg i, rfl⟩)
  have hsum : (⟨W.π.toLinearMap f, mem_Sring u (by rw [← hW.part]; exact ⟨f, hf, rfl⟩)⟩ : Sring (O := O) u) =
      ∑ i ∈ s, (⟨W.z i, hmemz i⟩ : Sring (O := O) u) * ⟨W.π (g i), hmemg i⟩ := by
    apply Subtype.ext

    simp [hfg, map_sum, WPres.z]

  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [map_mul, hzero i (Finset.mem_filter.mp hi).2, zero_mul]

theorem UpperTheory.V.UnitaryThreeInertia.isPtHom_sign :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K)
    (r : Γ →* GG (m := 3) (R := K)), IsPtHom u ξ r →
      (Upper F.η r ↔ ∀ j < 0, ∀ x (hx : x ∈ wpart (O := O) u j), ξ ⟨x, mem_Sring u hx⟩ = 0) ∧
      (Lower F.η r ↔ ∀ j > 0, ∀ x (hx : x ∈ wpart (O := O) u j), ξ ⟨x, mem_Sring u hx⟩ = 0) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu K _ _ ξ r hr
  obtain ⟨W, hW, _⟩ := exists_adapted F hF g₁ hg₁ u hu
  have hent : ∀ g a b, (r g).mat a b = ptMat u ξ g a b := fun g a b => by rw [(hr g).2]
  let Mp : AddSubmonoid ℤ :=
    { carrier := {n | 0 ≤ n}
      add_mem' := by
        intro a b ha hb
        show 0 ≤ a + b
        exact add_nonneg ha hb
      zero_mem' := le_refl (0 : ℤ) }
  let Mn : AddSubmonoid ℤ :=
    { carrier := {n | n ≤ 0}
      add_mem' := by
        intro a b ha hb
        show a + b ≤ 0
        exact add_nonpos ha hb
      zero_mem' := le_refl (0 : ℤ) }
  have hMp : ∀ n : ℤ, n ∈ Mp ↔ 0 ≤ n := fun _ => Iff.rfl
  have hMn : ∀ n : ℤ, n ∈ Mn ↔ n ≤ 0 := fun _ => Iff.rfl
  refine ⟨⟨fun hU j hj x hx => ?_, fun hv g hg a b hab => ?_⟩, ⟨fun hL j hj x hx => ?_, fun hv g hg a b hab => ?_⟩⟩
  · refine vanish_of_entries F u W hW ξ Mp (fun g hg a b hab => ?_) j (by rw [hMp]; omega) x hx
    rw [← hent]
    exact hU g ((MonoidHom.mem_ker).mpr hg) a b (by rw [hMp] at hab; omega)
  · rw [hent]
    exact hv (wt a b) hab _ (entry_mem u g a b)
  · refine vanish_of_entries F u W hW ξ Mn (fun g hg a b hab => ?_) j (by rw [hMn]; omega) x hx
    rw [← hent]
    exact hL g ((MonoidHom.mem_ker).mpr hg) a b (by rw [hMn] at hab; omega)
  · rw [hent]
    exact hv (wt a b) hab _ (entry_mem u g a b)
end
