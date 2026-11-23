module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

section

noncomputable section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob Topology

namespace GlobalTheory.CompanionTheory.FrobNz

private theorem three_halves_norm_sub_one_le_norm_sq_sub_one (u : ℂ) (hu : ‖u - 1‖ < 1/2) :
    3/2 * ‖u - 1‖ ≤ ‖u ^ 2 - 1‖ := by
  have h1 : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
  have h4 : ‖(2:ℂ)‖ ≤ ‖u + 1‖ + ‖u - 1‖ := by
    calc ‖(2:ℂ)‖ = ‖(u + 1) - (u - 1)‖ := by congr 1; ring
      _ ≤ ‖u + 1‖ + ‖u - 1‖ := norm_sub_le _ _
  have h5 : ‖(2:ℂ)‖ = 2 := by simp
  have h2 : (3:ℝ)/2 ≤ ‖u + 1‖ := by linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (u - 1), mul_le_mul_of_nonneg_left h2 (norm_nonneg (u - 1))]

private theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt' (w : ℂ) (hw : ∀ n : ℕ, ‖w ^ (2 ^ n) - 1‖ < 1/2) :
    w = 1 := by
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖w - 1‖ ≤ ‖w ^ (2 ^ n) - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : w ^ (2 ^ (n + 1)) = (w ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have h3 := three_halves_norm_sub_one_le_norm_sq_sub_one (w ^ (2 ^ n)) (hw n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖w - 1‖ = 3/2 * ((3/2) ^ n * ‖w - 1‖) := by ring
        _ ≤ 3/2 * ‖w ^ (2 ^ n) - 1‖ := by linarith
        _ ≤ ‖(w ^ (2 ^ n)) ^ 2 - 1‖ := h3
  by_contra hne
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1/2 / ‖w - 1‖) (by norm_num : (1:ℝ) < 3/2)
  have h1 := key n
  have h2 := hw n
  rw [div_lt_iff₀ hd] at hn
  linarith

theorem exists_compact_open_subgroup_trivial {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, χ k = 1 := by
  let V : Set G := {g | ‖(χ g : ℂ) - 1‖ < 1/2}
  have hVo : IsOpen V := isOpen_lt ((hχ.sub continuous_const).norm) continuous_const
  have h1V : (1 : G) ∈ V := by
    show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1/2
    simp
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : G)
  have hW : interior N ∩ V ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (interior_mem_nhds.mpr hN1) (hVo.mem_nhds h1V)
  obtain ⟨s, hs, h1s, hsW⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (X := G)).mem_nhds_iff.mp hW
  have hsclo : IsClopen s := hs
  have hsc : IsCompact s :=
    hNc.of_isClosed_subset hsclo.isClosed
      (hsW.trans (Set.inter_subset_left.trans interior_subset))
  obtain ⟨W, hW1, hWs⟩ := compact_open_separated_mul_right hsc hsclo.isOpen subset_rfl
  let H : Subgroup G :=
    { carrier := {g | ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s}
      mul_mem' := by
        intro a b ha hb
        change ∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha
        change ∀ x ∈ s, x * b ∈ s ∧ x * b⁻¹ ∈ s at hb
        change ∀ x ∈ s, x * (a * b) ∈ s ∧ x * (a * b)⁻¹ ∈ s
        intro x hx
        refine ⟨?_, ?_⟩
        · rw [← mul_assoc]; exact (hb _ (ha x hx).1).1
        · rw [mul_inv_rev, ← mul_assoc]; exact (ha _ (hb x hx).2).2
      one_mem' := by
        change ∀ x ∈ s, x * 1 ∈ s ∧ x * 1⁻¹ ∈ s
        intro x hx
        simp [hx]
      inv_mem' := by
        intro a ha
        change ∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha
        change ∀ x ∈ s, x * a⁻¹ ∈ s ∧ x * a⁻¹⁻¹ ∈ s
        intro x hx
        rw [inv_inv]
        exact ⟨(ha x hx).2, (ha x hx).1⟩ }
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) := by
    have hWW : W ∩ {g | g⁻¹ ∈ W} ∈ 𝓝 (1 : G) := Filter.inter_mem hW1 (inv_mem_nhds_one G hW1)
    refine Filter.mem_of_superset hWW ?_
    rintro g ⟨hg, hg'⟩
    show ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s
    intro x hx
    exact ⟨hWs (Set.mul_mem_mul hx hg), hWs (Set.mul_mem_mul hx hg')⟩
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_of_mem_nhds H hHn
  have hHs : (H : Set G) ⊆ s := by
    intro g hg
    have hg' : ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s := hg
    simpa using (hg' 1 h1s).1
  have hHc : IsCompact (H : Set G) :=
    hsc.of_isClosed_subset (Subgroup.isClosed_of_isOpen H hHo) hHs
  refine ⟨⟨H, hHo⟩, hHc, ?_⟩
  intro k hk
  have hkH : k ∈ H := hk
  apply Units.ext
  rw [Units.val_one]
  apply eq_one_of_forall_norm_pow_two_pow_sub_one_lt'
  intro n
  have hmem : k ^ (2 ^ n) ∈ H := H.pow_mem hkH _
  have hV : k ^ (2 ^ n) ∈ V := (hsW (hHs hmem)).2
  have hV' : ‖((χ (k ^ (2 ^ n)) : ℂˣ) : ℂ) - 1‖ < 1/2 := hV
  simpa [map_pow, Units.val_pow_eq_pow_val] using hV'

theorem exists_SB_integral_mul_char_eq_one : ∀ (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ),
    Continuous (fun g => (χ g : ℂ)) → ∃ α : SB G, ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ = 1 := by
  intro G _ _ _ _ _ _ _ _ μ _ χ hχ
  obtain ⟨K, hKc, hKχ⟩ := exists_compact_open_subgroup_trivial χ hχ
  have hKo : IsOpen (K : Set G) := K.isOpen
  have hKcl : IsClosed (K : Set G) := K.isClosed
  have hKm : MeasurableSet (K : Set G) := hKo.measurableSet
  have hpos : 0 < μ (K : Set G) := hKo.measure_pos μ ⟨1, one_mem K⟩
  have hfin : μ (K : Set G) < ⊤ := hKc.measure_lt_top
  have hr : (μ (K : Set G)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
  have hlc : ∀ c : ℂ, IsLocallyConstant ((K : Set G).indicator (fun _ => c)) := by
    intro c s
    by_cases hc : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
    · convert isOpen_univ using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert hKo using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert hKcl.isOpen_compl using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert isOpen_empty using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
  refine ⟨⟨(K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹), ?_⟩, ?_⟩
  · show IsLocallyConstant _ ∧ HasCompactSupport _
    exact ⟨hlc _,
      HasCompactSupport.intro hKc (fun x hx => Set.indicator_of_notMem hx _)⟩
  · have key : ∀ x, (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x * (χ x : ℂ) =
        (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x := by
      intro x
      by_cases hx : x ∈ (K : Set G)
      · rw [hKχ x hx, Units.val_one, mul_one]
      · rw [Set.indicator_of_notMem hx, zero_mul]
    show ∫ x, (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x * (χ x : ℂ) ∂μ = 1
    simp only [key]
    rw [integral_indicator_const _ hKm]
    simp [Measure.real, hpos.ne', hfin.ne, hr]

end GlobalTheory.CompanionTheory.FrobNz
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.AdmFL

variable {G X Y Z : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z]

theorem mem_fixed_iff {α : Representation ℂ G X} {K : Subgroup G} {x : X} :
    x ∈ fixed α K ↔ ∀ g ∈ K, α g x = x := by
  change (∀ h : K, α h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

private theorem finiteDimensional_fixed_of_exact_lemma {α : Representation ℂ G X}
    {β : Representation ℂ G Y} (i : α.IntertwiningMap β) (g : G) (x : X) :
    i (α g x) = β g (i x) := by
  have h := LinearMap.congr_fun (i.isIntertwining' g) x
  simpa [LinearMap.comp_apply] using h

theorem finiteDimensional_fixed_of_exact {α : Representation ℂ G X} {β : Representation ℂ G Y}
    {γ : Representation ℂ G Z} (i : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hi : Function.Injective i) (hker : ∀ y, p y = 0 → ∃ x, i x = y) (K : Subgroup G)
    [FiniteDimensional ℂ (fixed α K)] [FiniteDimensional ℂ (fixed γ K)] :
    FiniteDimensional ℂ (fixed β K) := by
  let j : fixed α K →ₗ[ℂ] fixed β K :=
    { toFun := fun x => ⟨i x, mem_fixed_iff.2 fun g hg => by
        rw [← finiteDimensional_fixed_of_exact_lemma i g x, mem_fixed_iff.1 x.2 g hg]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let q : fixed β K →ₗ[ℂ] fixed γ K :=
    { toFun := fun y => ⟨p y, mem_fixed_iff.2 fun g hg => by
        rw [← finiteDimensional_fixed_of_exact_lemma p g y, mem_fixed_iff.1 y.2 g hg]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hK : LinearMap.ker q ≤ LinearMap.range j := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hpy : p (y : Y) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := hker _ hpy
    have hxfix : x ∈ fixed α K := mem_fixed_iff.2 fun g hg => hi (by
      rw [finiteDimensional_fixed_of_exact_lemma i, hx, mem_fixed_iff.1 y.2 g hg])
    exact ⟨⟨x, hxfix⟩, Subtype.ext hx⟩
  refine ⟨?_⟩
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (f := q)
  · exact IsNoetherian.noetherian _
  · rw [Submodule.fg_iff_finiteDimensional]
    exact Submodule.finiteDimensional_of_le (le_trans inf_le_right hK)

private theorem isAdmissible_of_hasFiniteLength_lemma_3 {M : Type} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (g : G) (x : M) :
    Representation.ofModule' (k := ℂ) (G := G) M g x = MonoidAlgebra.single g (1 : ℂ) • x := by
  first
  | rfl
  | simp only [Representation.ofModule', MonoidAlgebra.lift_symm_apply, Algebra.lsmul_coe]

private theorem isAdmissible_of_hasFiniteLength_lemma_2 {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [Module (MonoidAlgebra ℂ G) M₁] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [Module (MonoidAlgebra ℂ G) M₂] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M₂]
    (f : M₁ →ₗ[MonoidAlgebra ℂ G] M₂) :
    ∃ φ : (Representation.ofModule' (k := ℂ) (G := G) M₁).IntertwiningMap
        (Representation.ofModule' (k := ℂ) (G := G) M₂), ∀ x, φ x = f x := by
  refine ⟨⟨f.restrictScalars ℂ, fun g => ?_⟩, fun x => rfl⟩
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, isAdmissible_of_hasFiniteLength_lemma_3,
    map_smul]

private theorem isAdmissible_of_hasFiniteLength_lemma_5 {M : Type} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [IsSimpleModule (MonoidAlgebra ℂ G) M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible := by
  have e : Subrepresentation (Representation.ofModule' (k := ℂ) (G := G) M) ≃o
      Submodule (MonoidAlgebra ℂ G) M :=
    { toFun := fun S =>
        { carrier := S.toSubmodule
          add_mem' := fun hx hy => S.toSubmodule.add_mem hx hy
          zero_mem' := S.toSubmodule.zero_mem
          smul_mem' := fun a x hx => by
            induction a using MonoidAlgebra.induction_on with
            | of g =>
              rw [MonoidAlgebra.of_apply, ← isAdmissible_of_hasFiniteLength_lemma_3]
              exact S.apply_mem_toSubmodule g hx
            | add a b ha hb =>
              rw [add_smul]
              exact S.toSubmodule.add_mem ha hb
            | smul r a ha =>
              rw [smul_assoc]
              exact S.toSubmodule.smul_mem r ha }
      invFun := fun P => ⟨P.restrictScalars ℂ, fun g v hv => by
        rw [Submodule.restrictScalars_mem, isAdmissible_of_hasFiniteLength_lemma_3]
        exact P.smul_mem _ hv⟩
      left_inv := fun S => by
        apply Subrepresentation.ext
        rfl
      right_inv := fun P => by
        ext x
        rfl
      map_rel_iff' := by
        intro S T
        exact Iff.rfl }
  exact e.isSimpleOrder

private theorem isAdmissible_of_hasFiniteLength_lemma_4 [TopologicalSpace G] (K : Subgroup G) :
    ∀ {M : Type} [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M], IsFiniteLength (MonoidAlgebra ℂ G) M →
    ∀ [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
      IsSubquotient σ (Representation.ofModule' (k := ℂ) (G := G) M) → σ.IsIrreducible → IsAdmissible σ) →
    IsOpen (K : Set G) → IsCompact (K : Set G) →
    FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) M) K) := by
  intro M _ _ hM
  induction hM with
  | of_subsingleton =>
    intro _ _ _ _ _
    infer_instance
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro _ _ hsub hKo hKc
    obtain ⟨i, hi⟩ := isAdmissible_of_hasFiniteLength_lemma_2 (G := G) N.subtype
    obtain ⟨p, hp⟩ := isAdmissible_of_hasFiniteLength_lemma_2 (G := G) N.mkQ
    have hinj : Function.Injective i := by
      intro x y hxy
      rw [hi, hi] at hxy
      exact Subtype.ext hxy
    have hker : ∀ y, p y = 0 → ∃ x, i x = y := by
      intro y hy
      rw [hp, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact ⟨⟨y, hy⟩, by rw [hi]; rfl⟩
    have hsurj : Function.Surjective p := by
      intro z
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective N z
      exact ⟨m, by rw [hp]; exact hm⟩
    have hNsub : IsSubquotient (Representation.ofModule' (k := ℂ) (G := G) N)
        (Representation.ofModule' (k := ℂ) (G := G) M) := IsSubquotient.of_injective i hinj
    haveI : FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) N) K) :=
      ih (fun W _ _ σ hσ hirr => hsub W σ (hσ.trans hNsub) hirr) hKo hKc
    haveI : FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) (M ⧸ N)) K) := by
      have hirr : (Representation.ofModule' (k := ℂ) (G := G) (M ⧸ N)).IsIrreducible :=
        isAdmissible_of_hasFiniteLength_lemma_5
      have hadm := hsub _ _ (IsSubquotient.of_surjective p hsurj) hirr
      unfold IsAdmissible at hadm
      exact hadm.2 K hKo hKc
    exact finiteDimensional_fixed_of_exact i p hinj hker K

theorem isAdmissible_of_hasFiniteLength : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), IsSubquotient σ ρ → σ.IsIrreducible → IsAdmissible σ) → IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ hsm hfl hirr
  unfold IsAdmissible
  refine ⟨hsm, fun K hKo hKc => ?_⟩
  letI instA : Module (MonoidAlgebra ℂ G) V := Module.compHom V ρ.asAlgebraHom.toRingHom
  haveI instT : IsScalarTower ℂ (MonoidAlgebra ℂ G) V := ⟨fun c a v => by
    show ρ.asAlgebraHom (c • a) v = c • ρ.asAlgebraHom a v
    rw [map_smul]
    rfl⟩
  have hρ : Representation.ofModule' (k := ℂ) (G := G) V = ρ := by
    ext g v
    rw [isAdmissible_of_hasFiniteLength_lemma_3]
    show ρ.asAlgebraHom (MonoidAlgebra.single g 1) v = ρ g v
    rw [Representation.asAlgebraHom_single_one]
  have hfl' : IsFiniteLength (MonoidAlgebra ℂ G) V := hfl
  have h := @isAdmissible_of_hasFiniteLength_lemma_4 G _ _ K V _ instA hfl' _ instT
    (fun W _ _ σ hσ h => hirr W σ (hρ ▸ hσ) h) hKo hKc
  rw [hρ] at h
  exact h

end GlobalTheory.CompanionTheory.AdmFL

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ExtTensorFixed

variable {G H V W X ι : Type} [DecidableEq ι] [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k : K, ρ (k : G) v = v := by
  show (∀ h : K, ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp

theorem coord_lTensor (b : Module.Basis ι ℂ X) (f : W →ₗ[ℂ] W) (y : X ⊗[ℂ] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (f.lTensor X y) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b y i) := by
  induction y with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul x w => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]

theorem mem_range_lTensor_fixed (σ : Representation ℂ G W) (K : Subgroup G) (y : X ⊗[ℂ] W)
    (hy : ∀ k : K, (σ (k : G)).lTensor X y = y) :
    y ∈ LinearMap.range ((fixed σ K).subtype.lTensor X) := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ X
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  have hc : ∀ i, e y i ∈ fixed σ K := fun i => (mem_fixed_iff σ K _).2 fun k => by
    have h := coord_lTensor b (σ (k : G)) y i
    rw [hy k] at h
    exact h.symm
  have hy' : y = (e y).sum fun i n => b i ⊗ₜ[ℂ] n := by
    have h : e.symm (e y) = _ := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (e y)
    exact (e.symm_apply_apply y).symm.trans h
  rw [hy']
  refine Submodule.sum_mem _ fun i _ => ⟨b i ⊗ₜ[ℂ] (⟨e y i, hc i⟩ : fixed σ K), ?_⟩
  simp

theorem fixed_le_range (ρ : Representation ℂ G V) (σ : Representation ℂ H W)
    (K₁ : Subgroup G) (K₂ : Subgroup H) :
    fixed (extTensor ρ σ) (K₁.prod K₂) ≤
      LinearMap.range (TensorProduct.map (fixed ρ K₁).subtype (fixed σ K₂).subtype) := by
  intro x hx
  have hx' := (mem_fixed_iff _ _ _).1 hx
  have act : ∀ (g : G × H) (z : V ⊗[ℂ] W),
      extTensor ρ σ g z = TensorProduct.map (ρ g.1) (σ g.2) z := by
    intro g z
    induction z with
    | add a c ha hc => simp [ha, hc]
    | tmul v w => simp

  have h1 : ∀ k : K₁, (ρ (k : G)).lTensor W (TensorProduct.comm ℂ V W x) =
      TensorProduct.comm ℂ V W x := by
    intro k
    have hk := hx' ⟨((k : G), 1), ⟨k.2, one_mem _⟩⟩
    rw [act] at hk
    conv_rhs => rw [← hk]
    simp only [map_one]
    generalize x = z
    induction z with
    | add a c ha hc => simp only [map_add (f := _), ha, hc]
    | tmul v w => simp
  obtain ⟨y', hy'⟩ := mem_range_lTensor_fixed ρ K₁ _ h1
  let y : (fixed ρ K₁) ⊗[ℂ] W := TensorProduct.comm ℂ W (fixed ρ K₁) y'
  have hy : (fixed ρ K₁).subtype.rTensor W y = x := by
    have : (fixed ρ K₁).subtype.rTensor W y =
        TensorProduct.comm ℂ W V ((fixed ρ K₁).subtype.lTensor W y') := by
      simp only [y]
      generalize y' = z
      induction z with
      | add a c ha hc => simp only [map_add (f := _), ha, hc]
      | tmul v w => simp
    rw [this, hy']
    simp

  have hinj : Function.Injective ((fixed ρ K₁).subtype.rTensor W) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have h2 : ∀ k : K₂, (σ (k : H)).lTensor (fixed ρ K₁) y = y := by
    intro k
    apply hinj
    have hk := hx' ⟨(1, (k : H)), ⟨one_mem _, k.2⟩⟩
    rw [act] at hk
    rw [hy]
    conv_rhs => rw [← hk, ← hy]
    simp only [map_one]
    generalize y = z
    induction z with
    | add a c ha hc => simp only [map_add (f := _), ha, hc]
    | tmul v w => simp
  obtain ⟨z, hz⟩ := mem_range_lTensor_fixed σ K₂ y h2
  refine ⟨z, ?_⟩
  rw [← hy, ← hz]
  generalize z = t
  induction t with
  | add a c ha hc => simp only [map_add (f := _), ha, hc]
  | tmul v w => simp

theorem finiteDimensional_fixed_extTensor : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ H W) (K₁ : Subgroup G) (K₂ : Subgroup H),
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K₁) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K₂) →
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (GlobalTheory.SmGL.extTensor ρ σ) (K₁.prod K₂)) := by
  intro G H V W _ _ _ _ _ _ ρ σ K₁ K₂ h₁ h₂
  exact Submodule.finiteDimensional_of_le (fixed_le_range ρ σ K₁ K₂)

end GlobalTheory.CompanionTheory.ExtTensorFixed
end
end
