module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle002
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PTestVeryCuspMulConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH HeckeM heckeAct)
open scoped Classical

namespace PositivityTheory.Rg.BcB.CG

theorem finH_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

theorem finHecke : FinHecke := by
  intro E _ _ _ a b _ _ ν _ A κ _ _ ψ U hψ hUo hUc hψU

  set K : Set (Hf E a b) := ⋃ x, ⋃ y, tsupport (ψ x y) with hK
  have hKc : IsCompact K := isCompact_iUnion fun x => isCompact_iUnion fun y => (hψ x y).2

  let C : Hf E a b ⧸ U → Set (Hf E a b) := fun q => (fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))
  have hCmem : ∀ q h, h ∈ C q ↔ (QuotientGroup.mk h : Hf E a b ⧸ U) = q := by
    intro q h
    show q.out⁻¹ * h ∈ U ↔ _
    rw [← QuotientGroup.eq]
    simp only [Quotient.out_eq]
    exact eq_comm
  have hCo : ∀ q, IsOpen (C q) := fun q => hUo.preimage (continuous_const.mul continuous_id)
  have hCm : ∀ q, MeasurableSet (C q) := fun q => (hCo q).measurableSet
  have hCf : ∀ q, ν (C q) ≠ ⊤ := by
    intro q
    show ν ((fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))) ≠ ⊤
    rw [measure_preimage_mul]
    exact hUc.measure_lt_top.ne
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover C hCo (by
    intro h _
    exact Set.mem_iUnion.2 ⟨QuotientGroup.mk h, (hCmem _ h).2 rfl⟩)
  have hin : ∀ h, (∀ x y, ψ x y h ≠ 0 → (QuotientGroup.mk h : Hf E a b ⧸ U) ∈ t) := by
    intro h x y hne
    have hhK : h ∈ K := Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, subset_tsupport _ hne⟩⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 (ht hhK)
    obtain ⟨hqt, hq⟩ := Set.mem_iUnion.1 hq
    rwa [(hCmem q h).1 hq]
  refine ⟨fun i j => if i.1 = j.1 then ∑ q ∈ t, Finsupp.single q.out ((ν (C q)).toReal * ψ i.2 j.2 q.out) else 0,
    ?_, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · intro p q x y
    simp
  · intro f hf
    funext i X
    simp only [convF, heckeAct]
    rw [Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single i.1 (fun p _ hp => by
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [if_neg (Ne.symm hp)]
      simp) (by simp)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [if_true]
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by ring)]
    set Φ : Hf E a b → ℂ := fun h => ψ i.2 z h * f (i.1, z) (X * finH h) with hΦ
    have hΦU : ∀ h, ∀ u ∈ U, Φ (h * u) = Φ h := by
      intro h u hu
      simp only [hΦ]
      rw [finH_mul, ← mul_assoc, hf _ u hu, hψU _ _ u hu h]
    have hΦout : ∀ h, Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out = Φ h := by
      intro h
      have h1 : ((QuotientGroup.mk h : Hf E a b ⧸ U).out)⁻¹ * h ∈ U := (hCmem _ h).2 rfl
      calc Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out
          = Φ ((QuotientGroup.mk h : Hf E a b ⧸ U).out * ((QuotientGroup.mk h : Hf E a b ⧸ U).out⁻¹ * h)) :=
            (hΦU _ _ h1).symm
        _ = Φ h := by rw [mul_inv_cancel_left]
    have hpt : Φ = fun h => ∑ q ∈ t, (C q).indicator (fun _ => Φ q.out) h := by
      funext h
      rw [Finset.sum_eq_single (QuotientGroup.mk h : Hf E a b ⧸ U)]
      · rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
      · intro q _ hq
        rw [Set.indicator_of_notMem]
        intro hc
        exact hq ((hCmem q h).1 hc).symm
      · intro hmem
        rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
        by_contra hne
        apply hmem
        refine hin h i.2 z ?_
        intro h0
        apply hne
        simp only [hΦ, h0, zero_mul]
    rw [hpt, integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hCm q), Finsupp.sum_single_index (by simp)]
      simp only [hΦ, Complex.real_smul, Measure.real]
      ring
    · intro q _
      exact (integrable_indicator_iff (hCm q)).2 (integrableOn_const (hCf q))

end PositivityTheory.Rg.BcB.CG

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH HeckeM heckeAct Repro)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

def ValCont : Prop := ∀ (n : ℕ) [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (k : Mat n → (M.V →L[ℂ] M.V))
  (val : Inf n → ℂ) (T : ℝ) (χ : ℕ → Inf n) (χ₀ : Inf n), IsMult μ M k val T →
  (∀ s m, Tendsto (fun j => GlobalTheory.Dec.gelfVal (χ j s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χ₀ s) m))) →
  Tendsto (fun j => val (χ j)) atTop (𝓝 (val χ₀))

def Pack : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
  ∀ (D : Dom E a b) [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
    [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
    (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] (κ : Type) [Fintype κ]
    (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (g : ℝ → ℝ)
    (ka' : Bool → ℕ → Kers Ma) (kb' : Bool → ℕ → Kers Mb) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (M : ℕ) (f : Io Ma Mb κ → H E a b → ℂ) (c : ℂ)
    (ca cb : InfinitePlace E → Bool → ℕ → ℂ), Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
    IsBump g T → (∀ v, IsKer μa (Ma v) [] g (ka v)) → (∀ v, IsKer μb (Mb v) [] g (kb v)) →
    (∀ s m v, IsKer μa (Ma v) [(s, m)] g (ka' s m v)) → (∀ s m v, IsKer μb (Mb v) [(s, m)] g (kb' s m v)) →
    IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) →
    (∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, ψ x y ((u₁, u₂) * h) = ψ x y h) →
    (∀ i, Continuous (f i)) → f ≠ 0 → LeftInv f → WL2 D M f → c ≠ 0 →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update ka v (ka' s m v)) kb ψ) f = ca v s m • f) →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens ka (Function.update kb v (kb' s m v)) ψ) f = cb v s m • f) →
    ∃ (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b),
      (∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m = ca v s m / c) ∧ (∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m = cb v s m / c) ∧
      EigAll χa χb f ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) ∧
      (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
      ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ)

theorem pack_of (h1 : TensTest) (h2 : TypeOf) (h3 : SmoothOf) (h4 : GrowthOf) (h5 : GelOf) (h6 : InfEx) (h7 : AutOf) :
    Pack := by
  intro E _ _ _ a b Ma Mb
  obtain ⟨W₁, W₂, f₁, f₂, hW⟩ := h2 E a b Ma Mb
  refine ⟨W₁, W₂, f₁, f₂, ?_⟩
  intro D _ _ _ _ _ _ μa _ μb _ ν _ κ _ ka kb va vb T ψ g ka' kb' K₁ K₂ M f c ca cb hC hka hkb hψ hg k0a k0b k1a k1b
    o₁ o₂ hlev hf hf0 hL hW2 hc he hea heb
  have hR : Repr D ka kb ψ f := ⟨hf, c, hc, he⟩
  have hty := hW D μa μb κ ka kb va vb T ψ K₁ K₂ f hka hkb hψ hlev hR
  obtain ⟨s₁, s₂⟩ := h3 E a b μa μb Ma Mb κ D ka kb va vb T ψ (K₁.prod K₂) f hka hkb hψ (o₁.prod o₂)
    (fun x y u hu h => hlev x y u.1 hu.1 u.2 hu.2 h) hR
  obtain ⟨C, N, hG⟩ := h4 E a b D _ _ M f c (h1 E a b μa μb Ma Mb κ ka kb va vb T ψ hka hkb hψ).1 hf hL hW2 hc he
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hf0
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hi₀
  have ga := fun v s m => (h5 E a b D μa μb ν Ma Mb κ ka kb va vb T ψ f c (ca v s m) v g s m hC hka hkb hψ hg ⟨s₁, s₂⟩ hf hc he).1
    _ (k0a v) (k1a s m v) (hea v s m)
  have gb := fun v s m => (h5 E a b D μa μb ν Ma Mb κ ka kb va vb T ψ f c (cb v s m) v g s m hC hka hkb hψ hg ⟨s₁, s₂⟩ hf hc he).2
    _ (k0b v) (k1b s m v) (heb v s m)
  have ea : ∀ v, ∃ χ : Inf a, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = ca v s m / c := fun v => by
    obtain ⟨φ, hφ⟩ := s₁ i₀ x₀.2
    refine h6 E a {φ} v (fun s m => ca v s m / c) ⟨φ, rfl, fun e => hx₀ ?_⟩ ?_
    · have := congrFun hφ x₀.1
      rw [e] at this
      exact this.symm
    · rintro _ rfl y s m x hx
      rw [hφ]
      exact ga v s m i₀ y x₀.2 x hx
  have eb : ∀ v, ∃ χ : Inf b, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = cb v s m / c := fun v => by
    obtain ⟨φ, hφ⟩ := s₂ i₀ x₀.1
    refine h6 E b {φ} v (fun s m => cb v s m / c) ⟨φ, rfl, fun e => hx₀ ?_⟩ ?_
    · have := congrFun hφ x₀.2
      rw [e] at this
      exact this.symm
    · rintro _ rfl y s m x hx
      rw [hφ]
      exact gb v s m i₀ y x₀.1 x hx
  choose χa hχa using ea
  choose χb hχb using eb
  have hE : EigAll χa χb f :=
    ⟨fun i v y m₂ s m x hx => by rw [hχa]; exact ga v s m i y m₂ x hx,
      fun i v y m₁ s m x hx => by rw [hχb]; exact gb v s m i y m₁ x hx⟩
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h7 E a b _ f K₁ K₂ W₁ W₂ χa χb C N o₁ o₂ f₁ f₂ hL hty hG hE
  exact ⟨χa, χb, hχa, hχb, hE, hty, s₁, s₂, a₁, a₂, a₃, a₄⟩

end PositivityTheory.Rg.BcB.CG

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical ComplexConjugate

namespace PositivityTheory.Rg.BcB.CG

theorem trace_mul_ent {n : ℕ} (M : KMod n) (A B : M.V →L[ℂ] M.V) :
    LinearMap.trace ℂ M.V ((A * B : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) = ∑ i, ∑ j, ent M A i j * ent M B j i := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ M.V)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((A * B : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) (stdOrthonormalBasis ℂ M.V i) =
      A (∑ j, inner ℂ (stdOrthonormalBasis ℂ M.V j) (B (stdOrthonormalBasis ℂ M.V i)) • stdOrthonormalBasis ℂ M.V j) := by
    rw [(stdOrthonormalBasis ℂ M.V).sum_repr']; rfl

  rw [h, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, ent, ent, mul_comm]

theorem phiOf_eq {n : ℕ} (M : KMod n) (Tθ : M.V →L[ℂ] M.V) (k : Mat n → (M.V →L[ℂ] M.V)) (y : G n) :
    phiOf M Tθ k y = ∑ p, ∑ q, ent M (k y.val) p q * ent M Tθ q p :=
  trace_mul_ent M _ _

theorem ent_adjoint {n : ℕ} (M : KMod n) [CompleteSpace M.V] (A : M.V →L[ℂ] M.V) (i j : Ix M) :
    ent M (ContinuousLinearMap.adjoint A) i j = conj (ent M A j i) := by
  simp only [ent]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem sum_pair {α β : Type} [Fintype α] [Fintype β] (X : α → α → ℂ) (Y : β → β → ℂ) :
    ∑ i : α × β, ∑ j : α × β, X i.1 j.1 * Y i.2 j.2 = (∑ p, ∑ q, X p q) * ∑ p, ∑ q, Y p q := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem sum_io {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ] (A A' : α → α → ℂ) (B B' : β → β → ℂ)
    (C D : κ → κ → ℂ) :
    ∑ i : (α × β) × κ, ∑ j : (α × β) × κ,
        A i.1.1 j.1.1 * B i.1.2 j.1.2 * C i.2 j.2 * (A' j.1.1 i.1.1 * B' j.1.2 i.1.2 * D j.2 i.2) =
      (∑ p, ∑ q, A p q * A' q p) * (∑ p, ∑ q, B p q * B' q p) * ∑ x, ∑ y, C x y * D y x := by
  calc _ = ∑ i : (α × β) × κ, ∑ j : (α × β) × κ,
          (A i.1.1 j.1.1 * A' j.1.1 i.1.1 * (B i.1.2 j.1.2 * B' j.1.2 i.1.2)) * (C i.2 j.2 * D j.2 i.2) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ p : α × β, ∑ q : α × β, A p.1 q.1 * A' q.1 p.1 * (B p.2 q.2 * B' q.2 p.2)) * ∑ x, ∑ y, C x y * D y x :=
        sum_pair (fun p q : α × β => A p.1 q.1 * A' q.1 p.1 * (B p.2 q.2 * B' q.2 p.2)) (fun x y => C x y * D y x)
    _ = _ := by
        rw [sum_pair (fun p q => A p q * A' q p) (fun p q => B p q * B' q p)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem prod_sum_ent (M : Mods E n) (A B : Ops M) :
    ∏ v, (∑ p, ∑ q, ent (M v) (A v) p q * ent (M v) (B v) q p) =
      ∑ P : IxA M, ∑ Q : IxA M, (∏ v, ent (M v) (A v) (P v) (Q v)) * ∏ v, ent (M v) (B v) (Q v) (P v) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun Q _ => ?_
  exact Finset.prod_mul_distrib

theorem tensTr : TensTr := by
  intro E _ _ _ a b Ma Mb κ _ ka kb Ta Tb ψ N g
  have ha := prod_sum_ent Ma (fun v => ka v (gInf v g.1).val) Ta
  have hb := prod_sum_ent Mb (fun v => kb v (gInf v g.2).val) Tb
  simp only [F.trM, tens, opM, entA, phiOf_eq]
  rw [ha, hb]
  exact sum_io (α := IxA Ma) (β := IxA Mb) (κ := κ)
    (fun P Q : IxA Ma => ∏ v, ent (Ma v) (ka v (gInf v g.1).val) (P v) (Q v))
    (fun Q P : IxA Ma => ∏ v, ent (Ma v) (Ta v) (Q v) (P v))
    (fun P Q : IxA Mb => ∏ v, ent (Mb v) (kb v (gInf v g.2).val) (P v) (Q v))
    (fun Q P : IxA Mb => ∏ v, ent (Mb v) (Tb v) (Q v) (P v)) (fun x y : κ => ψ x y (hFin g)) (fun y x : κ => N y x)

theorem gInf_eq (v : InfinitePlace E) (g : GA E n) :
    gInf v g = GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v)
      (GeneralLinearGroup.map (pInf E) g) := rfl

theorem continuous_hFin : Continuous (hFin (E := E) (a := a) (b := b)) :=
  ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.1.comp continuous_fst).prodMk ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.1.comp continuous_snd)

theorem hFin_inv (g : H E a b) : hFin g⁻¹ = (hFin g)⁻¹ :=
  Prod.ext (map_inv (gFin (E := E) (n := a)) g.1) (map_inv (gFin (E := E) (n := b)) g.2)

def ofComps (y : InfinitePlace E → G n) : GL (Fin n) (Cinf E) :=
  Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm y)

theorem continuous_ofComps : Continuous (ofComps (E := E) (n := n)) := by
  have hc : Continuous fun x : InfinitePlace E → Mat n =>
      (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm x :=
    continuous_matrix fun i j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  exact (Continuous.units_map _ hc).comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E => Mat n)).symm.continuous

theorem ofComps_gInf (g : GA E n) : ofComps (fun v => gInf v g) = GeneralLinearGroup.map (pInf E) g :=
  Units.ext (Matrix.ext fun _ _ => funext fun _ => rfl)

theorem hasCompactSupport_of_section {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {F : X → ℂ}
    (p : X → Y) (s : Y → X) (hs : Continuous s) (hsp : ∀ x, s (p x) = x) {K : Set Y} (hK : IsCompact K)
    (hF : ∀ x, F x ≠ 0 → p x ∈ K) : HasCompactSupport F :=
  HasCompactSupport.intro (hK.image hs) fun x hx => by
    by_contra h
    exact hx ⟨p x, hF x h, hsp x⟩

def ofParts (y : ((InfinitePlace E → G a) × (InfinitePlace E → G b)) × Hf E a b) : H E a b :=
  (infGL E a (ofComps y.1.1) * finGL E a y.2.1, infGL E b (ofComps y.1.2) * finGL E b y.2.2)

theorem continuous_ofParts : Continuous (ofParts (E := E) (a := a) (b := b)) :=
  (((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.2.1.comp (continuous_ofComps.comp (continuous_fst.comp continuous_fst))).mul
      ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.2.2.comp (continuous_fst.comp continuous_snd))).prodMk
    (((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.2.1.comp (continuous_ofComps.comp (continuous_snd.comp continuous_fst))).mul
      ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.2.2.comp (continuous_snd.comp continuous_snd)))

theorem ofParts_parts (g : H E a b) : ofParts ((fun v => gInf v g.1, fun v => gInf v g.2), hFin g) = g := by
  refine Prod.ext ?_ ?_
  · show infGL E a (ofComps fun v => gInf v g.1) * finGL E a (gFin g.1) = g.1
    rw [ofComps_gInf]; exact infGL_mul_finGL g.1
  · show infGL E b (ofComps fun v => gInf v g.2) * finGL E b (gFin g.2) = g.2
    rw [ofComps_gInf]; exact infGL_mul_finGL g.2

theorem entA_adjK (M : Mods E n) (k : Kers M) (i j : IxA M) (g : GA E n) :
    entA (adjK k) i j g = conj (entA k j i g⁻¹) := by
  simp only [entA, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have e : (gInf v g⁻¹).val = (gInf v g).val⁻¹ := by rw [map_inv]; exact Matrix.coe_units_inv _
  rw [e]
  have := FiniteDimensional.complete ℂ (M v).V
  exact ent_adjoint (M v) _ (i v) (j v)

theorem tens_entry {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [MeasurableSpace (G a)] [MeasurableSpace (G b)]
    {μa : Measure (G a)} {μb : Measure (G b)} {ka : Kers Ma} {kb : Kers Mb} {va vb} {T : ℝ}
    {ψ : Matrix κ κ (Hf E a b → ℂ)} (hA : IsMults μa ka va T) (hB : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (i j : Io Ma Mb κ) : Continuous (tens ka kb ψ i j) ∧ HasCompactSupport (tens ka kb ψ i j) := by
  set_option synthInstance.maxHeartbeats 200000 in
    have cA : ∀ v, Continuous fun y : G a => ent (Ma v) (ka v y.val) (i.1.1 v) (j.1.1 v) := fun v =>
      (mult_ent (hA v) _ _).1
    have cB : ∀ v, Continuous fun y : G b => ent (Mb v) (kb v y.val) (i.1.2 v) (j.1.2 v) := fun v =>
      (mult_ent (hB v) _ _).1
    refine ⟨?_, ?_⟩
    · exact ((continuous_finsetProd _ fun v _ => (cA v).comp ((continuous_gInf a v).comp continuous_fst)).mul
        (continuous_finsetProd _ fun v _ => (cB v).comp ((continuous_gInf b v).comp continuous_snd))).mul
        ((hψ i.2 j.2).1.comp continuous_hFin)
    · refine hasCompactSupport_of_section (fun g : H E a b => ((fun v => gInf v g.1, fun v => gInf v g.2), hFin g))
        ofParts continuous_ofParts ofParts_parts
        (K := (Set.univ.pi (fun v => tsupport fun y : G a => ent (Ma v) (ka v y.val) (i.1.1 v) (j.1.1 v)) ×ˢ
          Set.univ.pi (fun v => tsupport fun y : G b => ent (Mb v) (kb v y.val) (i.1.2 v) (j.1.2 v))) ×ˢ
          tsupport (ψ i.2 j.2))
        (((isCompact_univ_pi fun v => (mult_ent (hA v) _ _).2).prod
          (isCompact_univ_pi fun v => (mult_ent (hB v) _ _).2)).prod (hψ i.2 j.2).2) fun g hg => ?_
      have hg' : entA ka i.1.1 j.1.1 g.1 * entA kb i.1.2 j.1.2 g.2 * ψ i.2 j.2 (hFin g) ≠ 0 := hg
      obtain ⟨⟨h1, h2⟩, h3⟩ := mul_ne_zero_iff.1 hg' |>.imp_left mul_ne_zero_iff.1
      refine ⟨⟨fun v _ => subset_tsupport _ ?_, fun v _ => subset_tsupport _ ?_⟩, subset_tsupport _ h3⟩
      · exact Finset.prod_ne_zero_iff.1 h1 v (Finset.mem_univ v)
      · exact Finset.prod_ne_zero_iff.1 h2 v (Finset.mem_univ v)

theorem tensTest : TensTest := by
  intro E _ _ _ a b _ _ _ _ μa _ μb _ Ma Mb κ _ ka kb va vb T ψ hA hB hψ
  refine ⟨fun i j => tens_entry hA hB hψ i j, ?_⟩
  funext i j y
  show starRingEnd ℂ (tens ka kb ψ j i y⁻¹) = tens (adjK ka) (adjK kb) (adjF ψ) i j y
  simp only [tens, adjF, entA_adjK, map_mul, hFin_inv, Prod.fst_inv, Prod.snd_inv]

end PositivityTheory.Rg.BcB.CG

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)

namespace PositivityTheory.Rg.BcB.CG

def Test2J : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (R r : ℝ)
  (U : Subgroup (Hf E a b)), 0 ≤ R →
  (∀ v, Continuous (fa v) ∧ VeryCusp (fa v) ∧ ∀ y, fa v y ≠ 0 → lg y.val ≤ R) →
  (∀ v, Continuous (fb v) ∧ VeryCusp (fb v) ∧ ∀ y, fb v y ≠ 0 → lg y.val ≤ R) →
  HasCompactSupport ψ → IsOpen (U : Set (Hf E a b)) → (∀ u ∈ U, ∀ h, ψ (u * h) = ψ h ∧ ψ (h * u) = ψ h) →
  (∀ h, ψ h ≠ 0 → logSize (finGL E a h.1) ≤ r ∧ logSize (finGL E b h.2) ≤ r) →
  (∀ d x h₂, ψ (gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E a) x (ratGL E a d)), h₂) ≠ 0 → IsRegD d) →
  (∀ d x h₁, ψ (h₁, gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E b) x (ratGL E b d))) ≠ 0 → IsRegD d) →
  PositivityTheory.Rg.BcB.D4.IsTest2J (fun g : H E a b => (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g))
    (2 * Fintype.card (InfinitePlace E) * R + r)

theorem test2J : Test2J := fun E _ _ _ a b fa fb ψ R r U hR ha hb hψs hUo hψU hsz hr₁ hr₂ =>
  have h := pTest_main fa fb ψ R r U hR ha hb hψs hUo hψU hsz hr₁ hr₂
  { toIsTest2 := h.1, level := h.2 }

end PositivityTheory.Rg.BcB.CG
end
end
