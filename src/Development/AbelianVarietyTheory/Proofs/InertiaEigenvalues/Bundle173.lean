module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualOfDualSubgroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle061
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle148
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle143
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle151
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.GaussStable

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem NL_add [Unram F E] (A : Et F E) (y m : A.L) :
    A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star m * y) + A.NL m := by
  obtain ⟨-, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [map_add (f := _), map_add (f := _), hN, hN, hN, htr, star_add, star_mul, star_star]
  ring

theorem NL_zero [Unram F E] (A : Et F E) : A.NL 0 = 0 := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [hN, zero_mul, map_zero]

theorem formL_symm_nondeg [U : Unram F E] (A : Et F E) (v : A.Kˣ) :
    (EtMeas.formL A v).IsSymm ∧ (EtMeas.formL A v).Nondegenerate := by
  have := U.charZero
  have := EtMeas.finite_L A
  obtain ⟨-, hinj, -, htr, hnd⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hs : (EtMeas.formL A v).IsSymm := ⟨fun y y' => by
    rw [EtMeas.formL_apply, EtMeas.formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, EtMeas.formL A v y' y = 0) → y' = 0 := fun y' h => hnd y' fun y => by
    have h1 : (v : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := EtMeas.eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [EtMeas.formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  exact ⟨hs, ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩⟩


open scoped Classical in
open Classical in
theorem integral_indicator_char {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (χ : V → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) :
    ∫ m, (M : Set V).indicator χ m ∂μ = if ∀ m ∈ M, χ m = 1 then (μ.real (M : Set V) : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [show (M : Set V).indicator χ = (M : Set V).indicator (fun _ => (1 : ℂ)) from
      Set.indicator_congr (fun m hm => h m hm), integral_indicator_const _ hMo.measurableSet]
    simp
  · push Not at h
    obtain ⟨m0, hm0, h1⟩ := h
    refine AbsInv.integral_eq_zero_of_translate μ _ m0 (χ m0) h1 fun m => ?_
    by_cases hm : m ∈ M
    · rw [Set.indicator_of_mem (by exact M.add_mem hm hm0), Set.indicator_of_mem (by exact hm), hχ, mul_comm]
    · have h2 : m + m0 ∉ M := fun h' => hm (by simpa using M.sub_mem h' hm0)
      rw [Set.indicator_of_notMem (by exact h2), Set.indicator_of_notMem (by exact hm), mul_zero]

end GlobalTheory.JR.WeilQuad.GaussStable


open GlobalTheory.JR.WeilQuad.GaussStable in
theorem GlobalTheory.JR.WeilQuad.exists_stableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  intro F E _ _ _ _ hU A ψ x μ ω h u
  classical
  obtain ⟨-, -, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  set β := EtMeas.formL A ((u * x : A.Kˣ) : A.K) with hβ
  set f : A.L → ℂ := fun y => A.psiK ψ ((u : A.K) * x * A.NL y) with hf
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hin : Continuous fun y : A.L => Algebra.trace F A.K ((u : A.K) * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hflc : IsLocallyConstant f := (isLocallyConstant_of_stdChar hψ).comp_continuous hin
  have hfc : Continuous f := hflc.continuous
  have hkey : ∀ y m, f (y + m) = f y * ψ (β m y) * f m := by
    intro y m
    simp only [hf, hβ, EtMeas.formL_apply, Units.val_mul, NL_add A, Et.psiK, mul_add, map_add (f := _),
      AddChar.map_add_eq_mul]
  have hf0 : f 0 = 1 := by simp [hf, NL_zero A, Et.psiK]
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.L β
    (formL_symm_nondeg A (u * x)).1 (formL_symm_nondeg A (u * x)).2
  obtain ⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, -⟩ :=
    hsmall {y | f y = 1} ((hflc.isOpen_fiber 1).mem_nhds hf0)
  have hfM : ∀ m ∈ M, f m = 1 := fun m hm => hMU hm
  have hMpos : μ.real (M : Set A.L) ≠ 0 :=
    (ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hMc.measure_lt_top.ne).ne'
  refine ⟨∫ y in (N : Set A.L), f y ∂μ, M ⊔ N, AddSubgroup.isOpen_mono le_sup_left hMo, ?_, ?_⟩
  · refine (hMc.add hNc).of_isClosed_subset
      (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hMo)) ?_
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hz
    exact Set.add_mem_add ha hb
  intro Λ hΛo hΛc hle
  have hMΛ : M ≤ Λ := le_sup_left.trans hle
  have hNΛ : N ≤ Λ := le_sup_right.trans hle
  set iM : A.L → ℂ := (M : Set A.L).indicator (fun _ => 1) with hiM
  set iΛ : A.L → ℂ := (Λ : Set A.L).indicator (fun _ => 1) with hiΛ
  have hiMc : Continuous iM :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hMo, hMo⟩ continuous_const
  have hiΛc : Continuous iΛ :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hΛo, hΛo⟩ continuous_const
  let g : A.L → A.L → ℂ := fun m y => iM m * (iΛ y * f (y + m))
  have hgc : Continuous (Function.uncurry g) :=
    (hiMc.comp continuous_fst).mul ((hiΛc.comp continuous_snd).mul (hfc.comp (continuous_snd.add continuous_fst)))
  have hgs : HasCompactSupport (Function.uncurry g) := by
    refine HasCompactSupport.intro (hMc.prod hΛc) ?_
    rintro ⟨m, y⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : iM m = 0 := by rw [hiM, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
    · have : iΛ y = 0 := by rw [hiΛ, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
  have hswap := integral_integral_swap_of_hasCompactSupport hgc hgs (μ := μ) (ν := μ)
  have hA : ∀ m, ∫ y, g m y ∂μ = iM m * ∫ y in (Λ : Set A.L), f y ∂μ := by
    intro m
    by_cases hm : m ∈ M
    · have e : ∀ y, iΛ y * f (y + m) = (Λ : Set A.L).indicator f (y + m) := by
        intro y
        by_cases hy : y ∈ Λ
        · rw [hiΛ, Set.indicator_of_mem (by exact hy), Set.indicator_of_mem (by exact Λ.add_mem hy (hMΛ hm)), one_mul]
        · have h2 : y + m ∉ Λ := fun h' => hy (by simpa using Λ.sub_mem h' (hMΛ hm))
          rw [hiΛ, Set.indicator_of_notMem (by exact hy), Set.indicator_of_notMem (by exact h2), zero_mul]
      simp only [g]
      rw [integral_const_mul]
      congr 1
      simp_rw [e]
      rw [integral_add_right_eq_self (μ := μ) ((Λ : Set A.L).indicator f) m,
        integral_indicator hΛo.measurableSet]
    · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
      simp [g, h1]
  have hB : ∀ y, ∫ m, g m y ∂μ = (N : Set A.L).indicator (fun y => (μ.real (M : Set A.L) : ℂ) * f y) y := by
    intro y
    have e : ∀ m, g m y = iΛ y * f y * (M : Set A.L).indicator (fun m => ψ (β m y)) m := by
      intro m
      by_cases hm : m ∈ M
      · have h1 : iM m = 1 := by rw [hiM, Set.indicator_of_mem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = ψ (β m y) :=
          Set.indicator_of_mem (by exact hm) _
        simp only [g]
        rw [h1, h2, hkey, hfM m hm]; ring
      · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = 0 :=
          Set.indicator_of_notMem (by exact hm) _
        simp only [g]
        rw [h1, h2]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_indicator_char μ M hMo (fun m => ψ (β m y))
      (fun a b => by simp [map_add (f := _), AddChar.map_add_eq_mul])]
    by_cases hy : y ∈ N
    · rw [if_pos ((hN y).1 hy), Set.indicator_of_mem (by exact hy), hiΛ, Set.indicator_of_mem (by exact hNΛ hy)]
      ring
    · rw [if_neg (fun h' => hy ((hN y).2 h')), Set.indicator_of_notMem (by exact hy), mul_zero]
  have h1 : ∫ m, ∫ y, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (Λ : Set A.L), f y ∂μ := by
    simp_rw [hA]
    rw [integral_mul_const, hiM, integral_indicator_const _ hMo.measurableSet]
    simp
  have h2 : ∫ y, ∫ m, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (N : Set A.L), f y ∂μ := by
    simp_rw [hB]
    rw [integral_indicator hNo.measurableSet, integral_const_mul]
  have hmain := h1.symm.trans (hswap.trans h2)
  unfold gaussInt
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hMpos) hmain
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology

theorem sum_powerset_neg_one_pow_inter {ι : Type} [DecidableEq ι] (S J : Finset ι) (hJ : J ⊆ S) :
    ∑ I ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card = if J = ∅ then 2 ^ S.card else 0 := by
  have h1 : ∀ I : Finset ι, (-1 : ℝ) ^ (J ∩ I).card = ∏ i ∈ I, (if i ∈ J then (-1 : ℝ) else 1) := by
    intro I
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.filter_mem_eq_inter,
      Finset.inter_comm]
  have h2 : ∑ I ∈ S.powerset, (∏ i ∈ I, (if i ∈ J then (-1 : ℝ) else 1)) =
      ∏ i ∈ S, ((if i ∈ J then (-1 : ℝ) else 1) + 1) := by
    rw [Finset.prod_add]
    simp
  simp_rw [h1]
  rw [h2]
  split_ifs with hJe
  · subst hJe
    simp only [Finset.notMem_empty, if_false, Finset.prod_const]
    norm_num
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hJe
    exact Finset.prod_eq_zero (hJ hj) (by simp [hj])

theorem chi_cl_lift {K : UQ} (B : InvAlg K) {ι : Type} (e : ι → B.A) (I : Finset ι)
    (hmul : ∀ x y : B.A, IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y)
    (hnorm : ∀ w : B.A, IsUnit w → chi B e I (w * B.σ w) = 1) :
    ∃ F : B.Cl → ℚ, (∀ k, F k = chi B e I k.rep) ∧
      ∀ x : {x : B.Aˣ // B.σ (x : B.A) = x}, F (Quot.mk _ x) = chi B e I (x.1 : B.A) := by
  refine ⟨Quot.lift (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} => chi B e I (x.1 : B.A)) ?_, ?_, ?_⟩
  · rintro x y ⟨u, hu⟩
    rw [hu, hmul _ _ x.1.isUnit (u.isUnit.mul (u.isUnit.map B.σ)), hnorm _ u.isUnit, mul_one]
  · intro k
    conv_lhs => rw [← Quot.out_eq k]
    rfl
  · intro x; rfl

theorem sum_chi_mul_chi {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι) (hF : IsFrame B e π S) [Fintype B.Cl] (I₀ I : Finset ι) (h₀ : I₀ ⊆ S) (hI : I ⊆ S) :
    ∑ k : B.Cl, chi B e I₀ k.rep * chi B e I k.rep = if I = I₀ then (Fintype.card B.Cl : ℚ) else 0 := by
  obtain ⟨hmul, hnorm, hpi, -⟩ := GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B ι e π S hF
  split_ifs with hII
  · subst hII
    have : ∀ k : B.Cl, chi B e I k.rep * chi B e I k.rep = 1 := fun k => eta_sq _
    simp [this]
  · obtain ⟨j, hjS, hj⟩ : ∃ j ∈ S, ¬ (j ∈ I ↔ j ∈ I₀) := by
      by_contra hc
      push_neg at hc
      apply hII
      ext j
      constructor
      · intro h; exact (hc j (hI h)).1 h
      · intro h; exact (hc j (h₀ h)).2 h
    have hp : B.Plus (π j) := (hF.2 j hjS).1
    set v : B.Aˣ := hp.1.unit with hvdef
    have hvv : (v : B.A) = π j := hp.1.unit_spec
    have hv : B.σ (v : B.A) = v := by rw [hvv]; exact hp.2
    have hv' : B.σ ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) := by
      calc B.σ ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) * ((v : B.A) * B.σ ((v⁻¹ : B.Aˣ) : B.A)) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = ((v⁻¹ : B.Aˣ) : B.A) := by
            rw [← hv, ← map_mul, Units.mul_inv, map_one, mul_one]
    have hsign : chi B e I₀ (π j) * chi B e I (π j) = -1 := by
      have a0 := hpi I₀ {j} h₀ (Finset.singleton_subset_iff.2 hjS)
      have a1 := hpi I {j} hI (Finset.singleton_subset_iff.2 hjS)
      rw [Finset.prod_singleton] at a0 a1
      rw [a0, a1]
      by_cases hjI : j ∈ I
      · have hjI0 : j ∉ I₀ := fun h => hj ⟨fun _ => h, fun _ => hjI⟩
        simp [Finset.singleton_inter_of_mem hjI, Finset.singleton_inter_of_notMem hjI0]
      · have hjI0 : j ∈ I₀ := by by_contra h; exact hj ⟨fun h' => absurd h' hjI, fun h' => absurd h' h⟩
        simp [Finset.singleton_inter_of_mem hjI0, Finset.singleton_inter_of_notMem hjI]
    obtain ⟨F₀, hF₀, hF₀mk⟩ := chi_cl_lift B e I₀ (hmul I₀) (hnorm I₀)
    obtain ⟨F₁, hF₁, hF₁mk⟩ := chi_cl_lift B e I (hmul I) (hnorm I)
    let T : B.Cl → B.Cl := Quot.map
      (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} =>
        (⟨v * x.1, by rw [Units.val_mul, map_mul, hv, x.2]⟩ : {x : B.Aˣ // B.σ (x : B.A) = x}))
      (by rintro x y ⟨u, hu⟩; exact ⟨u, by simp only [Units.val_mul]; rw [hu, mul_assoc]⟩)
    let T' : B.Cl → B.Cl := Quot.map
      (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} =>
        (⟨v⁻¹ * x.1, by rw [Units.val_mul, map_mul, hv', x.2]⟩ : {x : B.Aˣ // B.σ (x : B.A) = x}))
      (by rintro x y ⟨u, hu⟩; exact ⟨u, by simp only [Units.val_mul]; rw [hu, mul_assoc]⟩)
    let E : B.Cl ≃ B.Cl :=
      { toFun := T, invFun := T'
        left_inv := fun k => Quot.inductionOn k fun x => congrArg (Quot.mk _) (Subtype.ext (inv_mul_cancel_left v x.1))
        right_inv := fun k => Quot.inductionOn k fun x => congrArg (Quot.mk _) (Subtype.ext (mul_inv_cancel_left v x.1)) }
    have key : ∀ k, F₀ (E k) * F₁ (E k) = -(F₀ k * F₁ k) := by
      intro k
      induction k using Quot.ind with
      | mk x =>
        change F₀ (Quot.mk _ _) * F₁ (Quot.mk _ _) = _
        rw [hF₀mk, hF₀mk, hF₁mk, hF₁mk, Units.val_mul, hmul I₀ _ _ v.isUnit x.1.isUnit,
          hmul I _ _ v.isUnit x.1.isUnit, hvv]
        linear_combination (chi B e I₀ (x.1 : B.A) * chi B e I (x.1 : B.A)) * hsign
    have hs : ∑ k : B.Cl, F₀ k * F₁ k = 0 := by
      have := Equiv.sum_comp E (fun k => F₀ k * F₁ k)
      simp only [key, Finset.sum_neg_distrib] at this
      linarith
    simpa [hF₀, hF₁] using hs

theorem sum_chi_ell_cl : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S → Finite B.Cl → ∀ (ℓ : B.A → ℝ) (h : Finset ι → ℝ),
    (∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) =
      (chi B e I x : ℝ) * h I) →
    ∀ I ⊆ S, ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card * h I := by
  intro K B ι _ _ e π S hF hfin ℓ h hyp I₀ h₀
  haveI := Fintype.ofFinite B.Cl
  have inv : ∀ x, B.Plus x → (2 : ℝ) ^ S.card * ℓ x = ∑ I ∈ S.powerset, (chi B e I x : ℝ) * h I := by
    intro x hx
    calc (2 : ℝ) ^ S.card * ℓ x
        = ∑ J ∈ S.powerset, (∑ I ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card) * ℓ ((∏ j ∈ J, π j) * x) := by
          rw [Finset.sum_eq_single ∅]
          · simp [sum_powerset_neg_one_pow_inter S ∅ (Finset.empty_subset _)]
          · intro J hJ hJe
            rw [sum_powerset_neg_one_pow_inter S J (Finset.mem_powerset.1 hJ), if_neg hJe, zero_mul]
          · intro hn; exact absurd (Finset.empty_mem_powerset S) hn
      _ = ∑ I ∈ S.powerset, ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) := by
          simp_rw [Finset.sum_mul]; exact Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun I hI => hyp I (Finset.mem_powerset.1 hI) x hx
  have hplus : ∀ k : B.Cl, B.Plus k.rep := fun k => ⟨(Quot.out k).1.isUnit, (Quot.out k).2⟩
  have e1 : ∀ k : B.Cl, ℓ k.rep = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I := by
    intro k; rw [← inv _ (hplus k), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have orth : ∀ I ∈ S.powerset, ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) =
      if I = I₀ then (Fintype.card B.Cl : ℝ) else 0 := by
    intro I hI
    have := sum_chi_mul_chi B e π S hF I₀ I h₀ (Finset.mem_powerset.1 hI)
    split_ifs at this ⊢ <;> exact_mod_cast this
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  simp_rw [e1]
  calc ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I)
      = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun k _ => by ring
    _ = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * (if I = I₀ then (Fintype.card B.Cl : ℝ) else 0) := by
        rw [Finset.sum_congr rfl fun I hI => by rw [orth I hI]]
    _ = (Fintype.card B.Cl : ℝ) / 2 ^ S.card * h I₀ := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_powerset.2 h₀, if_true]
        ring

end GlobalTheory.UnitLemma.Desc
end
end

section

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem sum_mulVec_smul {ι E EE D O : Type} [CommRing O] [CommRing E] [CommRing EE] [Algebra O E]
    [Algebra O EE] [AddCommGroup D] [Module EE D] (jE : (ι → E) →ₐ[O] EE) {r : ℕ} (b : Fin r → D)
    (A : ι → Matrix (Fin r) (Fin r) E) (y : ι → Fin r → E) :
    ∑ m, jE (fun i => (A i).mulVec (y i) m) • b m =
      ∑ k, jE (fun i => y i k) • ∑ m, jE (fun i => A i m k) • b m := by
  have h : ∀ m, (fun i => (A i).mulVec (y i) m) =
      ∑ k, ((fun i => y i k) * (fun i => A i m k) : ι → E) := by
    intro m
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

  simp only [h, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem isUnit_ι_E {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) : IsUnit (R.ι R.E) := by
  have hs : R.s ≠ 0 := by
    intro h
    have h1 := R.es
    have h2 := R.prime.two_le
    rw [h] at h1
    omega
  have h := R.EE_X.map R.φE
  rw [R.φE_ext, R.φ_X, map_mul, map_pow] at h
  exact (isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_right h)

theorem coord_comm_φ_γ : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∀ S : Sys R n r, (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (S.G i m k) : LetA O n) • (b m : W.DD T)) → (∀ k, (fun _ => j R.E : LetA O n) ^ S.M • W.φD T (b k : W.DD T) = ∑ m, (fun i => j (S.Φ i m k) : LetA O n) • (b m : W.DD T)) → (∀ x, coord W R jE T (fun k => (b k : W.DD T)) (S.φD x) = W.φD T (coord W R jE T (fun k => (b k : W.DD T)) x)) ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) (S.γD x) = W.γD T W.gam (coord W R jE T (fun k => (b k : W.DD T)) x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    _ hE _ S hγ hφ
  obtain ⟨hext, -, -, hφE, hγE⟩ := hE
  refine ⟨fun x => ?_, fun x => ?_⟩

  · rw [coord_apply, coord_apply, map_sum]
    refine (sum_mulVec_smul jE (fun k => (b k : W.DD T))
      (fun i => Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι)
      (fun i k => R.φE (x (i - 1) k))).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.φD_smul, ← hφE]
    congr 1
    have h1 : ∀ m, jE (fun i => (Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι) m k) =
        jE (fun _ => Ring.inverse (R.ι R.E)) ^ S.M *
          algebraMap (LetA O n) W.EE (fun i => j (S.Φ i m k)) := by
      intro m
      rw [← hext, ← map_pow, ← map_mul]
      rfl
    have h2 : jE (fun _ => Ring.inverse (R.ι R.E)) *
        algebraMap (LetA O n) W.EE (fun _ => j R.E) = 1 := by
      rw [← hext (fun _ => R.E), ← map_mul, ← map_one jE]
      congr 1
      funext i
      exact Ring.inverse_mul_cancel _ (isUnit_ι_E R)
    simp only [h1, mul_smul, algebraMap_smul]
    rw [← Finset.smul_sum, ← hφ, ← algebraMap_smul W.EE ((fun _ => j R.E : LetA O n) ^ S.M),
      smul_smul, map_pow, ← mul_pow, h2, one_pow,
      one_smul]

  · rw [coord_apply, coord_apply, map_sum]
    refine (sum_mulVec_smul jE (fun k => (b k : W.DD T))
      (fun i => (S.G i).map R.ι) (fun i k => R.γE (x i k))).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.γD_smul, ← hγE, hγ]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← algebraMap_smul W.EE (fun i => j (S.G i m k) : LetA O n), ← hext]
    rfl

end GlobalTheory.WachTie
end
end

section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

theorem _root_.GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra : ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) → (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) → (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) → ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) → ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S, (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧ ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  first | exact @GlobalTheory.part_projector_mem_adjoin | exact GlobalTheory.part_projector_mem_adjoin | (intros; apply GlobalTheory.part_projector_mem_adjoin <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTransfer

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def ExtIn (Y : Model Xo c β) (S : Set Y.X) (T : CDVR) (io : c.F →+* T.Fr) (x : Sp T.Fr ⟶ Xo.X) : Prop :=
  ∃ (y' : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), z ≫ pullback.fst _ _ = x ∧ z ≫ pullback.snd _ _ = spMap io ∧
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' ∧ Set.range y' ⊆ S

end GlobalTheory.GoodTransfer
end
end
