module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle006
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle020
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.BaireDistribution

section General

variable {X : Type} [TopologicalSpace X]

theorem indicator_mem {C : Set X} (hC : IsClopen C) (φ : SB X) : C.indicator φ.1 ∈ SB X := by
  refine ⟨?_, φ.2.2.mono fun x hx => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨U, hU, hxU, h⟩ := φ.2.1.exists_open x
      exact ⟨C ∩ U, hC.2.inter hU, ⟨hx, hxU⟩, fun y hy => by
        rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem hx, h y hy.2]⟩
    · exact ⟨Cᶜ, hC.1.isOpen_compl, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · rw [Set.support_indicator] at hx
    exact hx.2

theorem isCompact_support (φ : SB X) : IsCompact (Function.support φ.1) := by
  have h : IsClosed (Function.support φ.1) := by
    have := (φ.2.1 {0}).isClosed_compl
    convert this using 1
    ext x
    simp
  have h2 := φ.2.2.isCompact
  rwa [tsupport, h.closure_eq] at h2

theorem glue (D : SB X →ₗ[ℂ] ℂ) (𝒞 : Set X → Prop) (hcl : ∀ C, 𝒞 C → IsClopen C) (h0 : 𝒞 ∅)
    (hu : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C ∪ C')) (hi : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C ∩ C'))
    (hd : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C \ C')) (φ : SB X)
    (h : ∀ x ∈ Function.support φ.1, ∃ C, 𝒞 C ∧ x ∈ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0) : D φ = 0 := by
  have key : ∃ C, 𝒞 C ∧ Function.support φ.1 ⊆ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0 := by
    refine (isCompact_support φ).induction_on (p := fun s => ∃ C, 𝒞 C ∧ s ⊆ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, h0, subset_rfl, fun C' _ hC' ψ hψ => ?_⟩
      have : ψ = 0 := Subtype.ext (by rw [hψ, Set.subset_empty_iff.1 hC']; ext; simp)
      rw [this, map_zero]
    · rintro s t hst ⟨C, h1, h2, h3⟩
      exact ⟨C, h1, hst.trans h2, h3⟩
    · rintro s t ⟨C, h1, h2, h3⟩ ⟨E, e1, e2, e3⟩
      refine ⟨C ∪ E, hu _ _ h1 e1, Set.union_subset_union h2 e2, fun C' hC' hs ψ hψ => ?_⟩
      have a1 := h3 (C' ∩ C) (hi _ _ hC' h1) Set.inter_subset_right
        ⟨_, indicator_mem (hcl _ (hi _ _ hC' h1)) φ⟩ rfl
      have a2 := e3 (C' \ C) (hd _ _ hC' h1) (fun x hx => (hs hx.1).resolve_left hx.2)
        ⟨_, indicator_mem (hcl _ (hd _ _ hC' h1)) φ⟩ rfl
      have : ψ = ⟨_, indicator_mem (hcl _ (hi _ _ hC' h1)) φ⟩ +
          ⟨_, indicator_mem (hcl _ (hd _ _ hC' h1)) φ⟩ := by
        apply Subtype.ext
        rw [hψ]
        ext x
        by_cases a : x ∈ C' <;> by_cases b : x ∈ C <;> simp [Set.indicator, a, b]
      rw [this, map_add (f := _), a1, a2, add_zero]
    · intro x hx
      obtain ⟨C, h1, h2, h3⟩ := h x hx
      exact ⟨C, mem_nhdsWithin_of_mem_nhds ((hcl _ h1).2.mem_nhds h2), C, h1, subset_rfl, h3⟩
  obtain ⟨C, h1, h2, h3⟩ := key
  exact h3 C h1 subset_rfl φ (Set.indicator_eq_self.2 h2).symm

end General

section Group

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem isClopen_of_invariant {K : Subgroup G} (hK : IsOpen (K : Set G)) {C : Set G}
    (hC : ∀ a ∈ K, ∀ b ∈ K, ∀ g, a * g * b ∈ C ↔ g ∈ C) : IsClopen C := by
  have aux : ∀ S : Set G, (∀ a ∈ K, ∀ g ∈ S, a * g ∈ S) → IsOpen S := by
    intro S hS
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun y => y * g⁻¹) ⁻¹' K, fun y hy => ?_, hK.preimage (by fun_prop), by simp⟩
    simpa using hS _ hy g hg
  refine ⟨isOpen_compl_iff.1 (aux _ fun a ha g hg h => hg ?_), aux _ fun a ha g hg => ?_⟩
  · exact (hC a ha 1 K.one_mem g).1 (by simpa using h)
  · simpa using (hC a ha 1 K.one_mem g).2 hg


omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem doubleCoset_invariant (K : Subgroup G) (x : G) : ∀ a ∈ K, ∀ b ∈ K, ∀ g,
    a * g * b ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} ↔
      g ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} := by
  intro a ha b hb g
  constructor
  · rintro ⟨c, hc, d, hd, h⟩
    refine ⟨a⁻¹ * c, K.mul_mem (K.inv_mem ha) hc, d * b⁻¹, K.mul_mem hd (K.inv_mem hb), ?_⟩
    have : g = a⁻¹ * (a * g * b) * b⁻¹ := by group
    rw [this, h]; group
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c, K.mul_mem ha hc, d * b, K.mul_mem hd hb, by group⟩

theorem exists_nhds_invariant (φ : SB G) :
    ∃ U ∈ nhds (1 : G), ∀ a ∈ U, ∀ b ∈ U, ∀ g, φ.1 (a * g * b) = φ.1 g := by
  have h1 := GlobalTheory.OpTrace.isOpen_leftStabilizer φ.2.1 φ.2.2
  have h2 := GlobalTheory.OpTrace.isOpen_leftStabilizer (f := fun g => φ.1 g⁻¹)
    (φ.2.1.comp_continuous continuous_inv) (φ.2.2.comp_homeomorph (Homeomorph.inv G))
  refine ⟨_, (h1.inter h2).mem_nhds ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩,
    fun a ha b hb g => ?_⟩
  have e1 : ∀ g, φ.1 (a * g) = φ.1 g := ha.1
  have e2 : ∀ g, φ.1 (b * g)⁻¹ = φ.1 g⁻¹ := hb.2
  rw [mul_assoc, e1]
  simpa using (e2 (g * b)⁻¹).symm

end Group

theorem eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (ι : Type) [Countable ι] (K : ι → ℕ → Subgroup G), (∀ i m, IsOpen (K i m : Set G) ∧ IsCompact (K i m : Set G)) → (∀ i, ∀ U ∈ nhds (1 : G), ∃ m, (K i m : Set G) ⊆ U) → ∀ D : SB G →ₗ[ℂ] ℂ, (∀ x : G, ∃ i, ∀ (m : ℕ) (φ : SB G), φ.1 = Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0) → D = 0 := by
  intro G _ _ _ _ _ ι _ K hK hb D hD
  let O : Set G := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ φ : SB G, Function.support φ.1 ⊆ W → D φ = 0}
  have hO : IsOpen O := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨W, h1, h2, h3⟩
    exact ⟨W, fun y hy => ⟨W, h1, hy, h3⟩, h1, h2⟩
  have h1 : ∀ φ : SB G, Function.support φ.1 ⊆ O → D φ = 0 := by
    intro φ hφ
    refine glue D IsClopen (fun _ h => h) isClopen_empty (fun _ _ => IsClopen.union)
      (fun _ _ => IsClopen.inter) (fun _ _ => IsClopen.diff) φ fun x hx => ?_
    obtain ⟨W, w1, w2, w3⟩ := hφ hx
    obtain ⟨i, -⟩ := hD x
    obtain ⟨m, hm⟩ := hb i ((fun y => x * y) ⁻¹' W)
      ((w1.preimage (by fun_prop)).mem_nhds (by simpa using w2))
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' K i m, IsClopen.preimage
      ⟨(K i m).isClosed_of_isOpen (hK i m).1, (hK i m).1⟩ (by fun_prop), by simp,
      fun C' _ hC' ψ hψ => w3 ψ fun y hy => ?_⟩
    rw [hψ, Set.support_indicator] at hy
    simpa using hm (hC' hy.1)
  suffices hall : ∀ x, x ∈ O from LinearMap.ext fun φ => h1 φ fun x _ => hall x
  by_contra hne
  push_neg at hne
  let Z : ι → Set G := fun i => {x | ∀ (m : ℕ) (φ : SB G), φ.1 =
    Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0}
  haveI : LocallyCompactSpace (Oᶜ : Set G) := hO.isClosed_compl.locallyCompactSpace
  haveI : Nonempty (Oᶜ : Set G) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨i, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (X := (Oᶜ : Set G))
    (f := fun i => Subtype.val ⁻¹' closure (Z i))
    (fun i => isClosed_closure.preimage continuous_subtype_val)
    (Set.eq_univ_of_forall fun x => by
      obtain ⟨i, hi⟩ := hD x.1
      exact Set.mem_iUnion.2 ⟨i, subset_closure hi⟩)
  obtain ⟨t, t1, t2, t3⟩ := mem_interior.1 hy
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 t2
  refine y.2 ⟨W, hW, t3, fun φ hφ => ?_⟩
  obtain ⟨U, hU, hinv⟩ := exists_nhds_invariant φ
  obtain ⟨m, hm⟩ := hb i U hU
  refine glue D (fun C => ∀ a ∈ K i m, ∀ b ∈ K i m, ∀ g, a * g * b ∈ C ↔ g ∈ C)
    (fun C hC => isClopen_of_invariant (hK i m).1 hC) (by simp)
    (fun C C' h h' a ha b hb g => or_congr (h a ha b hb g) (h' a ha b hb g))
    (fun C C' h h' a ha b hb g => and_congr (h a ha b hb g) (h' a ha b hb g))
    (fun C C' h h' a ha b hb g => and_congr (h a ha b hb g) (not_congr (h' a ha b hb g))) φ
    fun x hx => ⟨_, doubleCoset_invariant (K i m) x,
      ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩, fun C hC hs ψ hψ => ?_⟩
  have hval : ∀ g ∈ C, φ.1 g = φ.1 x := fun g hg => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hs hg
    exact hinv a (hm ha) b (hm hb) x
  by_cases hCO : C ⊆ O
  · refine h1 ψ fun g hg => hCO ?_
    rw [hψ, Set.support_indicator] at hg
    exact hg.1
  obtain ⟨w, w1, w2⟩ := Set.not_subset.1 hCO
  have w3 : w ∈ closure (Z i) := t1 (show (⟨w, w2⟩ : (Oᶜ : Set G)) ∈ Subtype.val ⁻¹' W from
    hφ (show φ.1 w ≠ 0 by rw [hval w w1]; exact hx))
  obtain ⟨z, z1, z2⟩ := mem_closure_iff.1 w3 C (isClopen_of_invariant (hK i m).1 hC).2 w1
  have hCz : C = {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * z * b} := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hs hg
      obtain ⟨c, hc, d, hd, rfl⟩ := hs z1
      exact ⟨a * c⁻¹, mul_mem ha (inv_mem hc), d⁻¹ * b, mul_mem (inv_mem hd) hb, by group⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact (hC a ha b hb z).2 z1
  have hx' : φ.1 x ≠ 0 := hx
  have := z2 m ((φ.1 x)⁻¹ • ψ) (by
    rw [← hCz, Submodule.coe_smul, hψ]
    ext g
    by_cases hg : g ∈ C
    · simp [Set.indicator_of_mem hg, hval g hg, hx']
    · simp [Set.indicator_of_notMem hg])
  simpa [hx'] using this

end GlobalTheory.BaireDistribution
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter

namespace GlobalTheory.SBInduced

variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]


omit [IsTopologicalGroup G] in
theorem isClosedEmbedding_translate (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) (g : G) : IsClosedEmbedding fun y => r (j y) g := by
  have hc' : ∀ g, Continuous fun x => r x g := fun g => hc.comp (Continuous.prodMk_left g)
  let e : X ≃ₜ X :=
    { toFun := fun x => r x g
      invFun := fun x => r x g⁻¹
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := hc' g
      continuous_invFun := hc' g⁻¹ }
  exact e.isClosedEmbedding.comp hj

theorem isQuotientMap_sweep (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) :
    IsQuotientMap fun p : Y × K => r (j p.1) p.2 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : X × K ≃ₜ X × K :=
    { toFun := fun p => (r p.1 p.2, p.2)
      invFun := fun p => (r p.1 (p.2 : G)⁻¹, p.2)
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk
        continuous_snd
      continuous_invFun := (hc.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd).inv)).prodMk continuous_snd }
  have hcl : IsClosedMap fun p : Y × K => r (j p.1) p.2 :=
    (isClosedMap_fst_of_compactSpace (X := X) (Y := K)).comp
      (e.isClosedMap.comp (hj.prodMap (IsClosedEmbedding.id (X := K))).isClosedMap)
  refine hcl.isQuotientMap (hc.comp ((hj.continuous.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))) fun x => ?_
  obtain ⟨y, c, hc, rfl⟩ := hs x
  exact ⟨(y, ⟨c, hc⟩), rfl⟩

theorem descend [T2Space X] (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) (H : G → SB Y)
    (hU : ∀ᶠ u in 𝓝 (1 : G), ∀ g, H (g * u) = H g)
    (hfib : ∀ y g y' g', r (j y) g = r (j y') g' → (H g).1 y = (H g').1 y') :
    ∃ Φ : SB X, ∀ g y, Φ.1 (r (j y) g) = (H g).1 y := by
  have hq := isQuotientMap_sweep r h1 hm hc hj hK hs
  choose y c hcK hx using hs
  let φ : X → ℂ := fun x => (H (c x)).1 (y x)
  have hφ : ∀ g z, φ (r (j z) g) = (H g).1 z := fun g z => hfib _ _ _ _ (hx _).symm
  have hnear : ∀ g : G, ∀ᶠ z in 𝓝 g, H z = H g := fun g => by
    have hc : Tendsto (fun z : G => g⁻¹ * z) (𝓝 g) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact (hc.eventually hU).mono fun z hz => by simpa using hz g
  have hlc : IsLocallyConstant fun p : Y × G => (H p.2).1 p.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    filter_upwards [(continuous_snd.tendsto p).eventually (hnear p.2),
      (continuous_fst.tendsto p).eventually ((H p.2).2.1.eventually_eq p.1)] with z h₁ h₂
    rw [h₁, h₂]
  refine ⟨⟨φ, fun s => ?_, ?_⟩, hφ⟩
  · rw [← hq.isOpen_preimage]
    have := (hlc.comp_continuous (f := fun p : Y × K => (p.1, (p.2 : G)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) s
    convert this using 1
    ext p
    simp only [Set.mem_preimage, hφ, Function.comp_apply]
  · obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {z | H z = H x}) fun x _ => hnear x
    have hC : IsCompact (⋃ g ∈ t, tsupport (H g).1) :=
      t.isCompact_biUnion fun g _ => (H g).2.2
    refine HasCompactSupport.intro (((hC.image hj.continuous).prod hK).image hc) fun x hxn => ?_
    by_contra h0
    apply hxn
    obtain ⟨g, hg, hcg⟩ := Set.mem_iUnion₂.1 (ht (hcK x))
    refine ⟨(j (y x), c x), ⟨⟨y x, Set.mem_iUnion₂.2 ⟨g, hg, subset_tsupport _ ?_⟩, rfl⟩, hcK x⟩,
      (hx x).symm⟩
    rw [← show H (c x) = H g from hcg]
    exact h0

theorem sb_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  intro G X Y W _ _ _ _ _ _ _ _ r h1 hm hc j hj P K hK hs s hsP hP χ hχ σ ev hev
  have hχ' : ∀ᶠ u in 𝓝 (1 : G), χ u = 1 := IsOpen.mem_nhds hχ (one_mem χ.ker)
  have hce := isClosedEmbedding_translate r h1 hm hc hj
  let A : SB X → G → SB Y := fun Φ g => (χ g : ℂ) • ⟨fun y => Φ.1 (r (j y) g),
    Φ.2.1.comp_continuous (hce g).continuous, Φ.2.2.comp_isClosedEmbedding (hce g)⟩
  have hA : ∀ Φ g y, (A Φ g).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun _ _ _ => rfl
  have hext : ∀ w w' : W, (∀ y, (ev w).1 y = (ev w').1 y) → w = w' := fun w w' h =>
    ev.injective (Subtype.ext (funext h))
  let T : SB X →ₗ[ℂ] smoothPart (ind P σ) :=
    { toFun := fun Φ => ⟨⟨fun g => ev.symm (A Φ g), fun p g => hext _ _ fun y => by
          rw [hev, ev.apply_symm_apply, ev.apply_symm_apply, hA, hA, hm, hsP, map_mul, Units.val_mul,
            mul_assoc]⟩,
        mem_smoothPart_of_nhds (by
          filter_upwards [hχ', GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action G X r h1 hm hc Φ] with u hu hu'
          refine Subtype.ext (funext fun g => ?_)
          show ev.symm (A Φ (g * u)) = ev.symm (A Φ g)
          congr 1
          refine Subtype.ext (funext fun y => ?_)
          rw [hA, hA, map_mul, hu, mul_one, hm, hu'])⟩
      map_add' := fun Φ Ψ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (Φ + Ψ) g) = ev.symm (A Φ g) + ev.symm (A Ψ g)
        rw [← map_add (f := _)]
        congr 1
        exact Subtype.ext (funext fun y => mul_add _ _ _)))
      map_smul' := fun a Φ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (a • Φ) g) = a • ev.symm (A Φ g)
        rw [← map_smul]
        congr 1
        exact Subtype.ext (funext fun y => mul_left_comm _ _ _))) }
  have hT : ∀ Φ g y, (ev ((T Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun Φ g y => by
    show (ev (ev.symm (A Φ g))).1 y = _
    rw [ev.apply_symm_apply, hA]
  have hinj : Function.Injective T := fun Φ Ψ h => Subtype.ext (funext fun x => by
    obtain ⟨y, c, -, rfl⟩ := hs x
    have := hT Φ c y
    rw [h, hT] at this
    exact (mul_left_cancel₀ (χ c).ne_zero this).symm)
  have hsurj : Function.Surjective T := fun F => by
    have hF : ∀ᶠ u in 𝓝 (1 : G), ∀ x, F.1.1 (x * u) = F.1.1 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds F.2 (by simp)) fun g hg x =>
        congrFun (congrArg Subtype.val (show ind P σ g F.1 = F.1 from hg)) x
    obtain ⟨Φ, hΦ⟩ := descend r h1 hm hc hj hK hs (fun g => (χ g : ℂ)⁻¹ • ev (F.1.1 g))
      (by
        filter_upwards [hχ', hF] with u hu hu' g
        rw [hu', map_mul, hu, mul_one])
      (fun y g y' g' h => by
        have h2 : r (j y) (g * g'⁻¹) = j y' := by rw [hm, h, ← hm, mul_inv_cancel, h1]
        have hp := hP _ _ _ h2
        have h3 : s y ⟨_, hp⟩ = y' := hj.injective ((hsP y ⟨_, hp⟩).symm.trans h2)
        have h4 := F.1.2 ⟨_, hp⟩ g'
        rw [show ((⟨_, hp⟩ : P) : G) * g' = g from inv_mul_cancel_right g g'] at h4
        show (χ g : ℂ)⁻¹ * (ev (F.1.1 g)).1 y = (χ g' : ℂ)⁻¹ * (ev (F.1.1 g')).1 y'
        rw [h4, hev, h3]
        simp [← mul_assoc])
    refine ⟨Φ, Subtype.ext (Subtype.ext (funext fun g => hext _ _ fun y => ?_))⟩
    rw [hT, hΦ]
    exact mul_inv_cancel_left₀ (χ g).ne_zero _
  exact ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

end GlobalTheory.SBInduced
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

section
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem prodN_mul_apply {p : ℕ} {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} {g : GL (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (hg : InN p g) (r s : n ⊕ Fin c) (hrs : lev p s ≤ lev p r) :
    (h * g.val) r s = h r s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [hg s s le_rfl, Matrix.one_apply_eq, mul_one]
  · intro t _ hts
    by_cases hlt : lev p t < lev p r
    · rw [hh hlt, zero_mul]
    · rw [hg t s (hrs.trans (not_lt.mp hlt)), Matrix.one_apply_ne hts, mul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

theorem prodN_blockTriangular {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) :
    g.val.BlockTriangular (lev p) := by
  intro i j hij
  rw [hg i j hij.le, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

theorem prodN_inN_of_mem {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : InN p g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro r s _; simp
  | mul x y _ _ hx hy =>
    intro r s hrs
    rw [Units.val_mul, prodN_mul_apply (prodN_blockTriangular hx) hy r s hrs]
    exact hx r s hrs
  | inv x _ hx =>
    intro r s hrs
    have : Invertible x.val := ⟨x.inv, x.inv_val, x.val_inv⟩
    have hb : (x⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (prodN_blockTriangular hx)
    have key := prodN_mul_apply hb hx r s hrs
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, eq_comm] at key

end

end GlobalTheory.RootEx
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    substF h g (substF h' g' P) = substF (h * h') (g * g') P := by
  have key : (substF h g).comp (substF h' g') = substF (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, substF_X, substF_X]

    simp only [map_sum, map_mul, substF_X, algHom_C, algebraMap_eq, Pi.mul_apply, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

end GlobalTheory.CompactHowe

end
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.contDiff_fockGaussianFormOfLinearMap_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) →
    (∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t))) →
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.FockFamily.fockForm β (J t) x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => GlobalTheory.FockFamily.fockForm β (J p.1) p.2 p.2) := by
  first | exact @GlobalTheory.FockFamily.fockForm_family_contDiff | exact GlobalTheory.FockFamily.fockForm_family_contDiff | (intros; apply GlobalTheory.FockFamily.fockForm_family_contDiff <;> assumption)
end
