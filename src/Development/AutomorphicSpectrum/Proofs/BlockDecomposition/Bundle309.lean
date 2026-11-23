module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_cInd_restrict : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x} →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∃ K' ∈ 𝓝 (1 : G'), IsCompact K') →
    ∀ f : cIndSpace H σ, ∃ F : cIndSpace H' σ', ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  intro G G' W W' _ _ _ _ _ _ _ _ _ _ H H' ι σ σ' q hι hH hq hS hemb hcomp f
  obtain ⟨K', hK'n, hK'c⟩ := hcomp
  obtain ⟨L, hLo, hL⟩ := cInd_right_inv H σ f
  let b : G' → W' := fun x => q (f.1.1.1 (ι x))
  have hind : b ∈ indSpace H' σ' := by
    intro h x
    have hh : ι (h : G') ∈ H := (hH _).1 h.2
    have e : f.1.1.1 (((⟨ι h, hh⟩ : H) : G) * ι x) = σ ⟨ι h, hh⟩ (f.1.1.1 (ι x)) := f.1.1.2 ⟨ι h, hh⟩ (ι x)
    show q (f.1.1.1 (ι ((h : G') * x))) = σ' h (q (f.1.1.1 (ι x)))
    rw [map_mul, ← hq h hh]
    exact congrArg q e
  have hsm : (⟨b, hind⟩ : indSpace H' σ') ∈ smoothPart (ind H' σ') := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H' σ') (L.comap ι)
      (hLo.preimage hι) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show q (f.1.1.1 (ι (g * x))) = q (f.1.1.1 (ι g))
    rw [map_mul, hL (ι g) (ι x) hx]
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H' σ')) ∈ cIndSpace H' σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    have hD : IsCompact (C ∩ {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x}) := hC.inter_right hS
    have key : ∃ C' : Set G', IsCompact C' ∧ ∀ (x : G'), ∀ a ∈ H,
        ∀ n ∈ C ∩ {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x}, ι x = a * n →
        ∃ h' ∈ H', ∃ c' ∈ C', x = h' * c' := by
      refine hD.induction_on
        (p := fun A => ∃ C' : Set G', IsCompact C' ∧ ∀ (x : G'), ∀ a ∈ H, ∀ n ∈ A, ι x = a * n →
          ∃ h' ∈ H', ∃ c' ∈ C', x = h' * c') ?_ ?_ ?_ ?_
      · exact ⟨∅, isCompact_empty, fun _ _ _ n hn => absurd hn (Set.notMem_empty n)⟩
      · rintro A B hAB ⟨C', hC', h⟩
        exact ⟨C', hC', fun x a ha n hn e => h x a ha n (hAB hn) e⟩
      · rintro A B ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩
        refine ⟨C₁ ∪ C₂, hC₁.union hC₂, fun x a ha n hn e => ?_⟩
        rcases hn with hn | hn
        · obtain ⟨h', hh', c', hc', e'⟩ := h₁ x a ha n hn e
          exact ⟨h', hh', c', Or.inl hc', e'⟩
        · obtain ⟨h', hh', c', hc', e'⟩ := h₂ x a ha n hn e
          exact ⟨h', hh', c', Or.inr hc', e'⟩
      · rintro c ⟨-, h₀, hh₀, s, rfl⟩
        obtain ⟨K, hK, hKe⟩ := hemb K' hK'n
        have hcont : Continuous fun n : G => h₀⁻¹ * n * (ι s)⁻¹ := by fun_prop
        have hN : (fun n : G => h₀⁻¹ * n * (ι s)⁻¹) ⁻¹' K ∈ 𝓝 (h₀ * ι s) := by
          apply hcont.continuousAt.preimage_mem_nhds
          have e : h₀⁻¹ * (h₀ * ι s) * (ι s)⁻¹ = 1 := by group
          rw [e]
          exact hK
        refine ⟨_, mem_nhdsWithin_of_mem_nhds hN, (fun y => y * s) '' K',
          hK'c.image (by fun_prop), fun x a ha n hn e => ?_⟩
        have hn' : h₀⁻¹ * n * (ι s)⁻¹ ∈ K := hn
        have e2 : ι (x * s⁻¹) = (a * h₀) * (h₀⁻¹ * n * (ι s)⁻¹) := by
          rw [map_mul, map_inv, e]
          group
        obtain ⟨h', hh', κ', hκ', e3⟩ := hKe _ _ (mul_mem ha hh₀) _ hn' e2
        refine ⟨h', hh', κ' * s, ⟨κ', hκ', rfl⟩, ?_⟩
        rw [← mul_assoc, ← e3]
        group
    obtain ⟨C', hC', hkey⟩ := key
    refine ⟨C', hC', fun x hx => ?_⟩
    have hne : f.1.1.1 (ι x) ≠ 0 := by
      intro h0
      apply hx
      show q (f.1.1.1 (ι x)) = 0
      rw [h0, map_zero]
    obtain ⟨a, ha, c, hcC, e⟩ := hf (ι x) hne
    refine hkey x a ha c ⟨hcC, a⁻¹, inv_mem ha, x, ?_⟩ e
    rw [e]
    group
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, fun x => rfl⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem cIndSpace_apply_mem_mul {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] {H : Subgroup G}
    {σ : Representation ℂ H W} (f : GlobalTheory.PRep.cIndSpace H σ) (h : G) (hh : h ∈ H)
    (g : G) : f.1.1.1 (h * g) = σ ⟨h, hh⟩ (f.1.1.1 g) := by
  exact f.1.1.2 ⟨h, hh⟩ g

private theorem isHK_empty {G : Type} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H ∅ := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK
  exact ⟨fun _ _ _ => Iff.rfl, ⊤, by simp, fun _ _ _ => Iff.rfl⟩

private theorem isHK_union {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A ∪ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_union, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_union, hA₂ g x hx.1, hB₂ g x hx.2]

private theorem isHK_diff {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A \ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_diff, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_diff, hA₂ g x hx.1, hB₂ g x hx.2]

theorem exists_cInd_restrict_eq {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W') (hι : Continuous ι) (hσ : IsSmooth σ) (hsurj : Function.Surjective q)
    (hH : ∀ x, x ∈ H' ↔ ι x ∈ H)
    (hq : ∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w))
    (hemb : ∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ')
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (F : cIndSpace H' σ') : ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  classical
  obtain ⟨C, hC, hsupp⟩ : ∃ C : Set G', IsCompact C ∧
      ∀ g, F.1.1.1 g ≠ 0 → ∃ h ∈ H', ∃ c ∈ C, g = h * c := F.2
  have hloc : ∀ c : G', ∃ T : Set G, ∃ U ∈ 𝓝 c, GlobalTheory.CompanionTheory.LeibPhi.IsHK H T ∧
      (∀ y ∈ U, ι y ∈ T) ∧ ∃ e : GlobalTheory.PRep.cIndSpace H σ,
        ∀ x, ι x ∈ T → q (e.1.1.1 (ι x)) = F.1.1.1 x := by
    intro c
    obtain ⟨K', hK'o, hK'⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H' σ' F
    obtain ⟨w, hw⟩ := hsurj (F.1.1.1 c)
    obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_value H σ hσ hbase (ι c) w
    obtain ⟨Ke, hKeo, hKe⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H σ e
    have hS : {y : G' | c⁻¹ * y * c ∈ K' ∧ ι (c⁻¹ * y * c) ∈ Ke} ∈ 𝓝 (1 : G') := by
      have hcont : Continuous (fun y : G' => c⁻¹ * y * c) := by fun_prop
      have hopen : IsOpen {z : G' | z ∈ K' ∧ ι z ∈ Ke} := hK'o.inter (hKeo.preimage hι)
      exact (hopen.preimage hcont).mem_nhds (by simp [one_mem])
    obtain ⟨K, hK, hKemb⟩ := hemb _ hS
    have hconj : (fun μ : G => ι c * μ * (ι c)⁻¹) ⁻¹' K ∈ 𝓝 (1 : G) := by
      have hcont : Continuous (fun μ : G => ι c * μ * (ι c)⁻¹) := by fun_prop
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    obtain ⟨M, hMo, -, hMsub⟩ := hbase _ hconj
    refine ⟨{g | ∃ a ∈ H, ∃ x ∈ M, g = a * ι c * x}, {y | ι (c⁻¹ * y) ∈ M}, ?_,
      GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H M hMo (ι c), ?_, e, ?_⟩
    · have hcont : Continuous (fun y : G' => ι (c⁻¹ * y)) := hι.comp (continuous_const_mul c⁻¹)
      exact (hMo.preimage hcont).mem_nhds (by simp [one_mem])
    · intro y hy
      exact ⟨1, one_mem _, ι (c⁻¹ * y), hy, by simp⟩
    · rintro x ⟨a, ha, μ, hμ, hx⟩
      have hκ : ι c * μ * (ι c)⁻¹ ∈ K := hMsub hμ
      obtain ⟨h', hh', κ', hκ', hxeq⟩ := hKemb (x * c⁻¹) a ha (ι c * μ * (ι c)⁻¹) hκ
        (by rw [map_mul, hx, map_inv]; group)
      have hx' : x = h' * (c * (c⁻¹ * κ' * c)) := by
        have h0 : x = x * c⁻¹ * c := by group
        rw [h0, hxeq]
        group
      have hι' : ι h' ∈ H := (hH h').1 hh'
      have hFx : F.1.1.1 x = σ' ⟨h', hh'⟩ (q w) := by
        rw [hx', cIndSpace_apply_mem_mul F h' hh', hK' c _ hκ'.1, hw]
      rw [hFx, hx', map_mul, map_mul, cIndSpace_apply_mem_mul e _ hι',
        hKe _ _ hκ'.2, he]
      exact hq ⟨h', hh'⟩ hι' w
  choose T U hU hT hUT e he using hloc
  obtain ⟨t, -, hCt⟩ := hC.elim_nhds_subcover U (fun c _ => hU c)
  have hglue : ∀ s : Finset G', ∃ V : Set G, GlobalTheory.CompanionTheory.LeibPhi.IsHK H V ∧
      (∀ c ∈ s, T c ⊆ V) ∧ ∃ f : GlobalTheory.PRep.cIndSpace H σ,
        (∀ g ∉ V, f.1.1.1 g = 0) ∧ ∀ x, ι x ∈ V → q (f.1.1.1 (ι x)) = F.1.1.1 x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨∅, isHK_empty H, by simp, 0, fun g _ => ?_, fun x hx => ?_⟩
      · rfl
      · simp at hx
    | @insert c s hcs ih =>
      obtain ⟨V, hV, hsV, f, hf0, hf⟩ := ih
      obtain ⟨f', hf'in, hf'out⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H σ
        (isHK_diff (hT c) hV) (e c)
      have hadd : ∀ g, (f + f').1.1.1 g = f.1.1.1 g + f'.1.1.1 g := fun _ => rfl
      refine ⟨V ∪ T c, isHK_union hV (hT c), ?_, f + f', ?_, ?_⟩
      · intro d hd
        rcases Finset.mem_insert.1 hd with rfl | hd
        · exact Set.subset_union_right
        · exact (hsV d hd).trans Set.subset_union_left
      · intro g hg
        rw [Set.mem_union, not_or] at hg
        rw [hadd, hf0 g hg.1, hf'out g (fun h => hg.2 h.1), add_zero]
      · intro x hx
        by_cases hxV : ι x ∈ V
        · rw [hadd, hf'out _ (fun h => h.2 hxV), add_zero]
          exact hf x hxV
        · rcases hx with hx | hx
          · exact absurd hx hxV
          · rw [hadd, hf0 _ hxV, hf'in _ ⟨hx, hxV⟩, zero_add]
            exact he c x hx
  obtain ⟨V, hV, htV, f, hf0, hf⟩ := hglue t
  refine ⟨f, fun x => ?_⟩
  by_cases hx : ι x ∈ V
  · exact (hf x hx).symm
  · rw [hf0 _ hx, map_zero]
    by_contra hne
    obtain ⟨h', hh', c', hc', rfl⟩ := hsupp x hne
    obtain ⟨d, hd, hc'U⟩ := Set.mem_iUnion₂.1 (hCt hc')
    have hmem : ι c' ∈ V := htV d hd (hUT d c' hc'U)
    unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at hV
    apply hx
    rw [map_mul]
    exact (hV.1 _ ((hH h').1 hh') _).2 hmem

end GlobalTheory.CompanionTheory.LeibPhi
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenExists

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_subQuot [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (A B : Subrepresentation ρ) : IsSmooth (subQuot A B) := by
  have stab : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (w : W),
      ∃ H : Subgroup G, ∀ g, g ∈ H ↔ σ g w = w := by
    intro W _ _ σ w
    refine ⟨{ carrier := {g | σ g w = w}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · intro a b ha hb
      replace ha : σ a w = w := ha
      replace hb : σ b w = w := hb
      show σ (a * b) w = w
      rw [map_mul, Module.End.mul_apply, hb, ha]
    · show σ 1 w = w
      rw [map_one, Module.End.one_apply]
    · intro a ha
      replace ha : σ a w = w := ha
      show σ a⁻¹ w = w
      conv_lhs => rw [← ha]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  intro v
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨H₁, hH₁⟩ := stab ρ (x : V)
  obtain ⟨H₂, hH₂⟩ := stab (subQuot A B) (Submodule.Quotient.mk x)
  have hle : H₁ ≤ H₂ := by
    intro g hg
    rw [hH₁] at hg
    rw [hH₂]
    show Submodule.Quotient.mk (A.toRepresentation g x) = Submodule.Quotient.mk x
    congr 1
    exact Subtype.ext hg
  have e₁ : (H₁ : Set G) = {g | ρ g x = x} := Set.ext hH₁
  have e₂ : (H₂ : Set G) = {g | (subQuot A B) g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x} :=
    Set.ext hH₂
  rw [← e₂]
  exact Subgroup.isOpen_mono hle (e₁ ▸ hρ x)

theorem nontrivial_twJacquet_subQuot {ρ : Representation ℂ G V} (N : Subgroup G) (χ : N →* ℂˣ)
    (A B : Subrepresentation ρ) (hB : B.toSubmodule ≤ twKer ρ N χ) (hA : ¬ A.toSubmodule ≤ twKer ρ N χ) :
    Nontrivial (TwJacquet (subQuot A B) N χ) := by
  obtain ⟨a, haA, hak⟩ := SetLike.not_le_iff_exists.mp hA
  let φ : A.toSubmodule →ₗ[ℂ] V ⧸ twKer ρ N χ := (twKer ρ N χ).mkQ ∘ₗ A.toSubmodule.subtype
  have hφ : Submodule.comap A.toSubmodule.subtype B.toSubmodule ≤ LinearMap.ker φ := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (x : V) = (0 : V ⧸ twKer ρ N χ)
    rw [Submodule.Quotient.mk_eq_zero]
    exact hB (Submodule.mem_comap.mp hx)
  let Ψ := (Submodule.comap A.toSubmodule.subtype B.toSubmodule).liftQ φ hφ
  have hker : twKer (subQuot A B) N χ ≤ LinearMap.ker Ψ := by
    apply Submodule.span_le.mpr
    rintro w ⟨n, v, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul]
    show Submodule.Quotient.mk (ρ n (x : V)) - (χ n : ℂ) • Submodule.Quotient.mk (x : V) =
      (0 : V ⧸ twKer ρ N χ)
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨n, (x : V), rfl⟩
  refine ⟨⟨(Submodule.Quotient.mk (Submodule.Quotient.mk ⟨a, haA⟩ :
      A.toSubmodule ⧸ Submodule.comap A.toSubmodule.subtype B.toSubmodule) :
      _ ⧸ twKer (subQuot A B) N χ), 0, ?_⟩⟩
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  have h' := hker h
  rw [LinearMap.mem_ker] at h'
  have h'' : Submodule.Quotient.mk a = (0 : V ⧸ twKer ρ N χ) := h'
  exact hak ((Submodule.Quotient.mk_eq_zero _).mp h'')

end General

theorem exists_generic_subQuot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ →
    IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧
      IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ hfl hgen
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI := hNA.1
  haveI := hNA.2
  have hle : ∀ S T : Subrepresentation ρ, S.asSubmodule ≤ T.asSubmodule ↔ S ≤ T := fun S T => Iff.rfl
  have hsm : StrictMono (fun S : Subrepresentation ρ => S.asSubmodule) := fun S T h =>
    lt_of_le_of_ne ((hle S T).mpr h.le)
      (fun he => h.ne (le_antisymm ((hle S T).mp he.le) ((hle T S).mp he.ge)))
  have wfl : WellFounded (fun S T : Subrepresentation ρ => S < T) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_lt)
  have wfg : WellFounded (fun S T : Subrepresentation ρ => T < S) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_gt)
  have hgen' : Nontrivial (V ⧸ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := hgen
  let T0 : Subrepresentation ρ := ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
  have htop : ¬ T0.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    intro h
    obtain ⟨x, y, hxy⟩ := hgen'.exists_pair_ne
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hxy
    rw [Submodule.Quotient.eq]
    exact h Submodule.mem_top
  obtain ⟨A, hAP, hAmin⟩ := wfl.has_min {A | ¬ A.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N)} ⟨T0, htop⟩
  let Z : Subrepresentation ρ := ⟨⊥, fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]⟩
  have hZk : Z.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := bot_le
  have hZA : Z < A := by
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).mp hx
      rw [hx0]
      exact A.toSubmodule.zero_mem
    · intro h
      rw [← h] at hAP
      exact hAP hZk
  obtain ⟨B, hBA, hBmax⟩ := wfg.has_min {B | B < A} ⟨Z, hZA⟩
  have hcov : B ⋖ A := ⟨hBA, fun C hBC hCA => hBmax C hCA hBC⟩
  have hBk : B.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    by_contra h
    exact hAmin B h hBA
  exact ⟨A, B, hBA.le, GlobalTheory.SmGL.isIrreducible_subQuot hcov, GlobalTheory.CompanionTheory.GenExists.isSmooth_subQuot hρ A B,
    GlobalTheory.CompanionTheory.GenExists.nontrivial_twJacquet_subQuot _ _ A B hBk hAP⟩

end GlobalTheory.CompanionTheory.GenExists

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg

section Quot

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y]
  [Module ℂ Y]

end Quot

section Main

variable {k : Type} [Field k] [TopologicalSpace k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem isGeneric_of_surjective {τ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (q : τ.IntertwiningMap π) (hq : Function.Surjective q) (h : IsGeneric π) : IsGeneric τ := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  refine ⟨ψ, h1, h2, nontrivial_twJacquet_of_surjective q.toLinearMap hq
    (fun u v => Submodule.subset_span ⟨u, q v, ?_⟩) h3⟩
  rw [map_sub, map_smul]
  exact congrArg (· - _) (q.isIntertwining _ _ _ v)

end Main

end GlobalTheory.CompanionTheory.BZSeg

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CuspStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def prod₂MapR {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (π₁ : Representation ℂ (GL (Fin r) k) U)
    {π₂ : Representation ℂ (GL (Fin t) k) X} {π₂' : Representation ℂ (GL (Fin t) k) Y}
    (f : π₂.IntertwiningMap π₂') : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁ π₂') :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁ π₂')
    ⟨TensorProduct.map LinearMap.id f.toLinearMap, fun g => by
      ext u x
      exact congrArg (fun b => π₁ g.1 u ⊗ₜ[ℂ] b) (f.isIntertwining _ _ g.2 x)⟩ _)

def prod₂MapL {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {π₁ : Representation ℂ (GL (Fin r) k) X}
    {π₁' : Representation ℂ (GL (Fin r) k) Y} (f : π₁.IntertwiningMap π₁')
    (π₂ : Representation ℂ (GL (Fin t) k) U) : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁' π₂) :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁' π₂)
    ⟨TensorProduct.map f.toLinearMap LinearMap.id, fun g => by
      ext x u
      exact congrArg (fun b => b ⊗ₜ[ℂ] π₂ g.2 u) (f.isIntertwining _ _ g.1 x)⟩ _)

end GlobalTheory.CompanionTheory.CuspStd
end
end
