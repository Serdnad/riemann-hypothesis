module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommute
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle136
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle245
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.geometric_h1_zeta_sub_one_kills : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  intro p _ hp2 Ω _ _ hΩ T k j hj c hc hcoc
  classical
  let H := Ggeo p Ω ⊓ ⨅ n, Gn T n
  have uniform : ∃ S : Finset Ω, ∀ g ∈ H, ∀ h ∈ H,
      (∀ x ∈ S, h x = g x) → Cong (p := p) k (c h) (c g) := by
    have localTests : ∀ g : Gal p Ω, ∃ S : Finset Ω,
        (g ∈ H → ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong (p := p) k (c h) (c g)) ∧
        (g ∉ H → ∀ h ∈ H, ¬ ∀ x ∈ S, h x = g x) := by
      intro g
      by_cases hg : g ∈ H
      · obtain ⟨S, hS⟩ := hc.2 g hg
        exact ⟨S, fun _ => hS, fun h => (h hg).elim⟩
      · obtain ⟨a, hga, ha⟩ := TateGeo.exists_moved T hg
        refine ⟨{a}, fun h => (hg h).elim, fun _ h hh agree => hga ?_⟩
        exact (agree a (Finset.mem_singleton_self a)).symm.trans (ha h hh)
    choose S hlocal hsep using localTests
    obtain ⟨F, hF⟩ := GlobalTheory.T.finite_galois_approximation p Ω hΩ S
    refine ⟨F.biUnion S, fun g hg h hh agree => ?_⟩
    obtain ⟨g₀, hg₀F, hg₀⟩ := hF g
    have hg₀H : g₀ ∈ H := by
      by_contra h
      exact hsep g₀ h g hg hg₀
    have hg' := hlocal g₀ hg₀H g hg hg₀
    have hh' := hlocal g₀ hg₀H h hh (fun x hx =>
      (agree x (Finset.mem_biUnion.mpr ⟨g₀, hg₀F, hx⟩)).trans (hg₀ x hx))
    simpa [Cong] using Basic.cong_sub hh' hg'
  obtain ⟨S, hS⟩ := uniform
  obtain ⟨y, E, hy, hEH, hu, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hΩ T H inf_le_right S j hj
  let x : Ω := ∑ g ∈ E, g y * c g
  have hx : IsInt (p := p) x := by
    refine IsIntegral.sum _ fun g hg => ?_
    exact (IsIntegral.map g.toAlgHom hy).mul (hc.1 g (hEH g hg))
  refine ⟨-x, hx.neg, fun h hh => ?_⟩
  have hσ : ∀ g ∈ E, ∃ g' ∈ E, h (g y) = g' y ∧ ∀ s ∈ S, h (g s) = g' s := by
    intro g hg
    obtain ⟨g', ⟨hg', hy', hs'⟩, -⟩ := hu (h * g) (H.mul_mem hh (hEH g hg))
    exact ⟨g', hg', hy', hs'⟩
  choose! σ hσE hσy hσS using hσ
  have hσinj : Set.InjOn σ E := by
    intro g₁ hg₁ g₂ hg₂ e
    apply (hu g₁ (hEH g₁ hg₁)).unique ⟨hg₁, rfl, fun _ _ => rfl⟩
    refine ⟨hg₂, h.injective ?_, fun s hs => h.injective ?_⟩
    · rw [hσy g₁ hg₁, hσy g₂ hg₂, e]
    · rw [hσS g₁ hg₁ s hs, hσS g₂ hg₂ s hs, e]
  have himage : E.image σ = E :=
    Finset.eq_of_subset_of_card_le (by simpa only [Finset.image_subset_iff] using hσE)
      (by rw [Finset.card_image_of_injOn hσinj])
  have hperm : ∑ g ∈ E, σ g y * c (σ g) = x := by
    rw [← Finset.sum_image (f := fun g' => g' y * c g') hσinj, himage]
  have hhx : h x = ∑ g ∈ E, h (g y) * h (c g) := by
    simp only [x, map_sum, map_mul]
  have hζ : h (T.ζ j) = T.ζ j := (((TateGeo.mem_geoTop_iff T h).mp hh).2 j).1
  have hsumh : ∑ g ∈ E, h (g y) = T.ζ j - 1 := by
    rw [← map_sum, hsum, map_sub, map_one, hζ]
  have termCong : ∀ g ∈ E, Cong (p := p) k (h (g y) * h (c g))
      (σ g y * c (σ g) - h (g y) * c h) := by
    intro g hg
    have hgH := hEH g hg
    obtain ⟨a, ha, ea⟩ := hcoc h hh g hgH
    obtain ⟨b, hb, eb⟩ := hS (σ g) (hEH _ (hσE g hg)) (h * g) (H.mul_mem hh hgH) (hσS g hg)
    refine ⟨h (g y) * (b - a), (IsIntegral.map h.toAlgHom (IsIntegral.map g.toAlgHom hy)).mul (hb.sub ha), ?_⟩
    rw [← hσy g hg]
    linear_combination h (g y) * (eb - ea)
  have sumCong (s : Finset (Gal p Ω)) (f f' : Gal p Ω → Ω)
      (hs : ∀ g ∈ s, Cong (p := p) k (f g) (f' g)) :
      Cong (p := p) k (∑ g ∈ s, f g) (∑ g ∈ s, f' g) := by
    induction s using Finset.induction_on with
    | empty => simpa using Basic.cong_refl (p := p) k (0 : Ω)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact Basic.cong_add (hs a (Finset.mem_insert_self a s))
        (ih fun g hg => hs g (Finset.mem_insert_of_mem hg))
  have total := sumCong E _ _ termCong
  rw [← hhx, Finset.sum_sub_distrib, hperm, ← Finset.sum_mul, hsumh] at total
  obtain ⟨z, hz, e⟩ := total
  refine ⟨z, hz, ?_⟩
  show (T.ζ j - 1) * c h - (h (-x) - -x) = _
  rw [map_neg]
  linear_combination e
end

section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ

theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := by rw [h]; exact Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hd := hmem Complex.I hI
  simp only [Set.diff_empty] at hd
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hle : nhdsWithin Complex.I {Complex.I}ᶜ ≤ Filter.principal Hs :=
    le_trans nhdsWithin_le_nhds (Filter.le_principal_iff.2 (hopen.mem_nhds hI))
  have hbot : nhdsWithin Complex.I {Complex.I}ᶜ = ⊥ := by
    have := hd.mono_right hle
    exact disjoint_self.1 this
  exact (NormedField.nhdsNE_neBot Complex.I).ne hbot

theorem siegel_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → siegel T c x ≠ 0 := by
  intro Ω _ _ _ ε T c x hx h0
  have han := GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hx
  rw [h0, map_zero] at han
  have hev : (fun z => sgC c x z) =ᶠ[Filter.codiscreteWithin Hs] (fun _ => (0 : ℂ)) :=
    (Filter.Germ.coe_eq.1 han.symm)
  have hne : ∀ᶠ z in Filter.codiscreteWithin Hs, sgC c x z ≠ 0 := by
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    have hz' : 0 < z.im := hz
    simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact sg_ne_zero c x _ hx
  haveI := codiscreteWithin_Hs_neBot
  obtain ⟨z, h1, h2⟩ := (hev.and hne).exists
  exact h2 h1

end GlobalTheory.KZ
end

section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

noncomputable section

namespace GlobalTheory.KZDist

lemma isAdmissibleSmoothingFactor_divided_indices (c m : ℕ) (x : Fin 2 → ℚ) (a b : ℕ) (hA : GlobalTheory.Sieg.admitted c x) (hm : 0 < m) :
    GlobalTheory.Sieg.admitted c ![(x 0 + a) / m, (x 1 + b) / m] := by
  obtain ⟨hc1, hc6, hnot⟩ := hA
  refine ⟨hc1, hc6, ?_⟩
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk hl
  apply hnot
  refine ⟨⟨m * k - c * a, ?_⟩, ⟨m * l - c * b, ?_⟩⟩
  · push_cast; rw [hk]; field_simp; ring
  · push_cast; rw [hl]; field_simp; ring

lemma isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [← Filter.forall_mem_nonempty_iff_neBot]
  intro s hs
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs'.mem_nhds hI)
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  rcases hz1 with h | h
  · exact ⟨z, h⟩
  · exact absurd hz2 h

theorem siegel_distribution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (m : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, siegel T c ![(x 0 + a) / m, (x 1 + b) / m] = siegel T c x := by
  intro Ω _ _ _ ε T c m x hA hm hcm
  haveI := codiscreteWithin_Hs_neBot
  apply T.an.injective
  rw [map_prod, GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hA]
  simp_rw [map_prod]
  have h1 : ∀ a ∈ Finset.range m, ∏ b ∈ Finset.range m, T.an (siegel T c ![(x 0 + a) / m, (x 1 + b) / m])
      = Filter.Germ.coeRingHom _ (∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m]) := by
    intro a _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c _ (isAdmissibleSmoothingFactor_divided_indices c m x a b hA hm)]
    rfl
  rw [Finset.prod_congr rfl h1, ← map_prod]
  show ((∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m] : ℂ → ℂ) : Mero) = _
  congr 1
  funext z
  simpa only [Finset.prod_apply, sgC] using
    GlobalTheory.SiegDist.sg_distribution c m x (UpperHalfPlane.ofComplex z) hA hm hcm

end GlobalTheory.KZDist
end
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelSL

theorem isOpen_Hs : IsOpen Hs := by
  show IsOpen {z : ℂ | 0 < z.im}
  exact isOpen_lt continuous_const Complex.continuous_im

theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := h ▸ Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by
    show (0 : ℝ) < Complex.I.im
    simp
  have h1 := hmem Complex.I hI
  rw [Set.sdiff_empty, Filter.disjoint_principal_right] at h1
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)
  have h3 := Filter.inter_mem h1 h2
  rw [Set.compl_inter_self] at h3
  simpa using Filter.nonempty_of_mem h3

theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  apply Filter.Germ.coe_eq.2
  filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
  exact h z hz

theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  simp [sgC, UpperHalfPlane.ofComplex_apply]

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem an_injective {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) :
    Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

theorem siegel_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ} {f : T.K}
    (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) : siegel T c x = f := by
  have hex : ∃ g : T.K, T.an g = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  apply an_injective T
  rw [siegel, dite_eq_left hex, hex.choose_spec, hf]

theorem sl_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ)
    (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), GlobalTheory.Sieg.admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  intro Ω _ _ _ ε T c x γ hx
  symm
  apply siegel_eq
  rw [T.an_sl _ _ _ (GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hx)]
  apply germ_eq_of_eqOn
  intro z hz
  have hτ : ((⟨z, hz⟩ : ℍ) : ℂ) = z := rfl
  rw [← hτ, mob_ofSL, sgC_coe, sgC_coe, GlobalTheory.T.siegel_function_transformation c x γ _ hx]

end GlobalTheory.KZ.SiegelSL
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.modularTowerB_admissibleHecke_commute : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T T' : Letter, admitted N l T → admitted N l T' → ∀ b ∈ X.B N l w, X.op N l T (X.op N l T' b) = X.op N l T' (X.op N l T b) := by
  first | exact @GlobalTheory.KZ.B_op_comm | exact GlobalTheory.KZ.B_op_comm | (intros; apply GlobalTheory.KZ.B_op_comm <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant : ∀ (D : D7) (N : ℕ) (J : Subgroup (GA D N)), J ≤ intG D N → ∀ g, gam D J g ≠ 0 ∧ gam D J g ∣ 8 ^ (2 * fF D * N) * (2 * (2 * fF D * N)).factorial ∧ ∀ γ ∈ ratG D N, ∀ j ∈ J, gam D J (γ * g * j) = gam D J g := by
  first | exact @GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant | exact GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant | (intros; apply GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_integral_sum_conj_eq_zeta_sub_one : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (S : Finset Ω), (∀ s ∈ S, IsInt (p := p) s) → ∀ j : ℕ, 1 ≤ j →
  ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧ (∀ g ∈ E, g ∈ ⨅ n, Gn T n) ∧
    (∀ h ∈ ⨅ n, Gn T n, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
    ∑ g ∈ E, g y = T.ζ j - 1 := by
  first | exact @GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top | exact GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top | (intros; apply GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.ShareThm

theorem real_step (ep x w₁ w₂ W₁ W₂ D D₀ D₁ D₂ : ℝ) (h0 : 0 ≤ ep) (h1 : ep < 1) (hD : 0 ≤ D)
    (hall : |D - x| ≤ ep * x) (h₁ : |D₁ - w₁ * x| ≤ ep * (w₁ * x)) (h₂ : |D₂ - w₂ * x| ≤ ep * (w₂ * x))
    (hw₁ : w₁ ≤ W₁) (hw₂ : w₂ ≤ W₂) (hs : D ≤ D₀ + D₁ + D₂) :
    (1 - (1 + ep) / (1 - ep) * (max 0 W₁ + max 0 W₂)) * D ≤ D₀ := by
  obtain ⟨ha, hb⟩ := abs_le.mp hall
  have hc := (abs_le.mp h₁).2
  have hd := (abs_le.mp h₂).2
  have hx : 0 ≤ x := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hpos : 0 < 1 - ep := by linarith
  have hxD : x ≤ D / (1 - ep) := by
    rw [le_div_iff₀ hpos]; nlinarith
  have m₁ : w₁ ≤ max 0 W₁ := hw₁.trans (le_max_right _ _)
  have m₂ : w₂ ≤ max 0 W₂ := hw₂.trans (le_max_right _ _)
  have p₁ : 0 ≤ max 0 W₁ := le_max_left _ _
  have p₂ : 0 ≤ max 0 W₂ := le_max_left _ _
  set A := max 0 W₁
  set B := max 0 W₂
  have e₁ : D₁ + D₂ ≤ (1 + ep) * ((w₁ + w₂) * x) := by nlinarith
  have e₂ : (w₁ + w₂) * x ≤ (A + B) * (D / (1 - ep)) :=
    (mul_le_mul_of_nonneg_right (add_le_add m₁ m₂) hx).trans
      (mul_le_mul_of_nonneg_left hxD (add_nonneg p₁ p₂))
  have e₃ : D₁ + D₂ ≤ (1 + ep) * ((A + B) * (D / (1 - ep))) :=
    e₁.trans (mul_le_mul_of_nonneg_left e₂ (by linarith))
  have e₄ : (1 - (1 + ep) / (1 - ep) * (A + B)) * D = D - (1 + ep) * ((A + B) * (D / (1 - ep))) := by
    ring
  rw [e₄]; linarith

theorem abstract_step (H₁ H₂ : Type) [Group H₁] [Fintype H₁] [Group H₂] [Fintype H₂]
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (H₁ × H₂) M)
    (U₁ : H₁ → Prop) (U₂ : H₂ → Prop) (E₁ A₁ : H₁ → ℂ) (E₂ A₂ : H₂ → ℂ)
    (hE₁ : IsProj E₁) (hE₂ : IsProj E₂) (hA₁ : IsProj A₁) (hA₂ : IsProj A₂)
    (c₁ : ∀ a, conv A₁ a = conv a A₁) (c₂ : ∀ a, conv A₂ a = conv a A₂)
    (u₁ : ∀ γ, E₁ γ ≠ 0 → U₁ γ) (u₂ : ∀ γ, E₂ γ ≠ 0 → U₂ γ)
    (w₁ w₂ W₁ W₂ : ℝ) (hw₁ : conv (dirac - A₁) E₁ 1 = (w₁ : ℂ) * E₁ 1) (hw₂ : conv (dirac - A₂) E₂ 1 = (w₂ : ℂ) * E₂ 1)
    (hW₁ : w₁ ≤ W₁) (hW₂ : w₂ ≤ W₂) (ep c : ℝ) (h0 : 0 ≤ ep) (h1 : ep < 1)
    (hc : ∀ e : H₁ × H₂ → ℂ, IsProj e → ((∀ γ, e γ ≠ 0 → U₁ γ.1) ∨ ∀ γ, e γ ≠ 0 → U₂ γ.2) →
      |(rk ρ e : ℝ) - c * (e 1).re| ≤ ep * (c * (e 1).re)) :
    (1 - (1 + ep) / (1 - ep) * (max 0 W₁ + max 0 W₂)) * (rk ρ (tens2 E₁ E₂) : ℝ)
      ≤ (rk ρ (conv (tens2 A₁ A₂) (tens2 E₁ E₂)) : ℝ) := by
  obtain ⟨hop, hone, -, -, -, -, -⟩ := GlobalTheory.T.groupAlgebraOperator_convolution_calculus (H₁ × H₂) M ρ
  obtain ⟨-, -, has₁, hd₁, hp₁, hq₁, -⟩ := GlobalTheory.T.groupAlgebraOperator_convolution_calculus H₁ ℂ 1
  obtain ⟨-, -, has₂, hd₂, hp₂, hq₂, -⟩ := GlobalTheory.T.groupAlgebraOperator_convolution_calculus H₂ ℂ 1
  obtain ⟨-, -, tc, tp, td, ts⟩ := GlobalTheory.T.exteriorTensorProduct_convolution_calculus Unit H₁ H₂
  have P₁ : IsProj (conv (dirac - A₁) E₁) := hp₁ _ _ (hq₁ _ hA₁) hE₁ (by
    rw [(has₁ dirac A₁ E₁).2.1, (has₁ dirac A₁ E₁).2.2, (hd₁ E₁).1, (hd₁ E₁).2, c₁])
  have P₂ : IsProj (conv (dirac - A₂) E₂) := hp₂ _ _ (hq₂ _ hA₂) hE₂ (by
    rw [(has₂ dirac A₂ E₂).2.1, (has₂ dirac A₂ E₂).2.2, (hd₂ E₂).1, (hd₂ E₂).2, c₂])
  have kall := hc (tens2 E₁ E₂) (tp _ _ hE₁ hE₂) (Or.inr fun γ h => u₂ _ (right_ne_zero_of_mul h))
  have k₁ := hc (tens2 (conv (dirac - A₁) E₁) E₂) (tp _ _ P₁ hE₂) (Or.inr fun γ h => u₂ _ (right_ne_zero_of_mul h))
  have k₂ := hc (tens2 E₁ (conv (dirac - A₂) E₂)) (tp _ _ hE₁ P₂) (Or.inl fun γ h => u₁ _ (left_ne_zero_of_mul h))
  have v₁ : c * (tens2 (conv (dirac - A₁) E₁) E₂ 1).re = w₁ * (c * (tens2 E₁ E₂ 1).re) := by
    simp only [tens2, Prod.fst_one, Prod.snd_one, hw₁, mul_assoc, Complex.re_ofReal_mul]; ring
  have v₂ : c * (tens2 E₁ (conv (dirac - A₂) E₂) 1).re = w₂ * (c * (tens2 E₁ E₂ 1).re) := by
    simp only [tens2, Prod.fst_one, Prod.snd_one, hw₂]
    rw [mul_left_comm (E₁ 1), Complex.re_ofReal_mul]; ring
  rw [v₁] at k₁
  rw [v₂] at k₂
  have hs := GlobalTheory.T.finrank_range_le_sum_three_complements M (op ρ (tens2 E₁ E₂)) (op ρ (tens2 A₁ dirac)) (op ρ (tens2 dirac A₂))
  have r₀ : op ρ (tens2 A₁ dirac) * op ρ (tens2 dirac A₂) * op ρ (tens2 E₁ E₂)
      = op ρ (conv (tens2 A₁ A₂) (tens2 E₁ E₂)) := by
    rw [← (hop _ _).1, ← (hop _ _).1, tc A₁ dirac, (hd₁ A₁).2, (hd₂ A₂).1]
  have r₁ : (1 - op ρ (tens2 A₁ dirac)) * op ρ (tens2 E₁ E₂) = op ρ (tens2 (conv (dirac - A₁) E₁) E₂) := by
    rw [← hone, ← td, ← (hop _ _).2.1, ← (ts dirac A₁ dirac dirac).1, ← (hop _ _).1, tc, (hd₂ E₂).1]
  have r₂ : (1 - op ρ (tens2 dirac A₂)) * op ρ (tens2 E₁ E₂) = op ρ (tens2 E₁ (conv (dirac - A₂) E₂)) := by
    rw [← hone, ← td, ← (hop _ _).2.1, ← (ts dirac dirac dirac A₂).2, ← (hop _ _).1, tc, (hd₁ E₁).1]
  rw [r₀, r₁, r₂] at hs
  refine real_step ep _ w₁ w₂ W₁ W₂ _ _ _ _ h0 h1 (Nat.cast_nonneg _) kall k₁ k₂ hW₁ hW₂ ?_
  unfold rk
  exact_mod_cast hs

theorem level_proj (g : ℕ) [Fact g.Prime] (N : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) :
    IsProj (tens fun v => (L v).e) ∧ ∀ γ, (tens fun v => (L v).e) γ ≠ 0 → AllUnip γ := by
  constructor
  · refine (GlobalTheory.T.exteriorTensorProduct_convolution_calculus ι (GG g N) Unit).2.1 _ fun v => ?_
    obtain ⟨a, b, c, d, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N (L v)
    exact (GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) ℂ 1 _ _ a b c d).1
  · intro γ h v
    apply (GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N (L v)).2.2.2.2
    have h' : (L v).e (γ v) ≠ 0 := Finset.prod_ne_zero_iff.mp h v (Finset.mem_univ v)
    by_contra hn
    exact h' (by simp [Lev.e, eps, hn])

theorem bad_share : ∀ (g₁ g₂ : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (N m q d : ℕ) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂], 100000 ≤ N → PrimeOK g₁ q d → PrimeOK g₂ q d → ∀ (L₁ : ι₁ → Lev g₁ N) (L₂ : ι₂ → Lev g₂ N) (τ₁ : ι₁ → (ZMod g₁)[X] → GG g₁ N → ℂ) (τ₂ : ι₂ → (ZMod g₂)[X] → GG g₂ N → ℂ), (∀ v, IsSeries (τ₁ v)) → (∀ v, IsSeries (τ₂ v)) → ∀ (ch₁ : ι₁ → Fin m → (ZMod g₁)ˣ) (ch₂ : ι₂ → Fin m → (ZMod g₂)ˣ) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) (ep : ℝ), 0 ≤ ep → ep < 1 → CountAt ρ ep → (1 - (1 + ep) / (1 - ep) * (max 0 (badBound g₁ (Fintype.card ι₁) m N ((min q d : ℕ) : ℝ)) + max 0 (badBound g₂ (Fintype.card ι₂) m N ((min q d : ℕ) : ℝ)))) * (rk ρ (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e)) : ℝ) ≤ (rk ρ (conv (tens2 (eGood τ₁ ch₁) (eGood τ₂ ch₂)) (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e))) : ℝ) := by
  intro g₁ g₂ _ _ N m q d ι₁ ι₂ _ _ hN ok₁ ok₂ L₁ L₂ τ₁ τ₂ s₁ s₂ ch₁ ch₂ M _ _ _ ρ ep h0 h1 hc
  obtain ⟨c, -, hc⟩ := hc
  obtain ⟨pE₁, u₁⟩ := level_proj g₁ N ι₁ L₁
  obtain ⟨pE₂, u₂⟩ := level_proj g₂ N ι₂ L₂
  obtain ⟨pA₁, c₁⟩ := GlobalTheory.T.goodTupleProjector_isProj_central g₁ N m ι₁ τ₁ ch₁ s₁
  obtain ⟨pA₂, c₂⟩ := GlobalTheory.T.goodTupleProjector_isProj_central g₂ N m ι₂ τ₂ ch₂ s₂
  obtain ⟨w₁, hw₁, hW₁⟩ := GlobalTheory.T.badLabelTuple_weight_le_bound g₁ N m q d ι₁ L₁ τ₁ ch₁ hN ok₁ s₁
  obtain ⟨w₂, hw₂, hW₂⟩ := GlobalTheory.T.badLabelTuple_weight_le_bound g₂ N m q d ι₂ L₂ τ₂ ch₂ hN ok₂ s₂
  exact abstract_step _ _ M ρ AllUnip AllUnip _ _ _ _ pE₁ pE₂ pA₁ pA₂ c₁ c₂ u₁ u₂ w₁ w₂ _ _ hw₁ hw₂ hW₁ hW₂
    ep c h0 h1 hc

end GlobalTheory.BadShare.ShareThm
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

theorem _root_.GlobalTheory.T.heisenbergReproducingKernelSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  first | exact @GlobalTheory.UnitaryTheta.KerSum.kerSum_spec | exact GlobalTheory.UnitaryTheta.KerSum.kerSum_spec | (intros; apply GlobalTheory.UnitaryTheta.KerSum.kerSum_spec <;> assumption)
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

theorem _root_.GlobalTheory.T.integral_cexp_herm_gaussian_eq_div_det : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  first | exact @GlobalTheory.UnitaryTheta.integral_gaussian_unitary | exact GlobalTheory.UnitaryTheta.integral_gaussian_unitary | (intros; apply GlobalTheory.UnitaryTheta.integral_gaussian_unitary <;> assumption)
end
