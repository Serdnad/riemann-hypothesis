module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle040
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle056
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
import Mathlib.RingTheory.Henselian
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

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.AdaptedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_pow_le {ϖ : kˣ} (h : IsUnif ϖ) (s : kˣ) :
    ∀ᶠ e : ℕ in Filter.atTop, valuation k ((ϖ ^ e : kˣ) : k) ≤ valuation k (s : k) := by
  have h1 : valuation k (ϖ : k) < 1 := (h _).2 le_rfl
  have hs : valuation k (s : k) ≠ 0 := by simp
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hs)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le he).trans hm.le

theorem eventually_subset_cball {ϖ : kˣ} (h : IsUnif ϖ) {K : Set k} (hK : IsCompact K) :
    ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹ := by
  have key : ∀ s : kˣ, ∀ᶠ e : ℕ in Filter.atTop, cball s ⊆ cball (ϖ ^ e)⁻¹ := by
    intro s
    filter_upwards [eventually_pow_le h s⁻¹] with e he x hx
    have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
    have he0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := by
      rw [pos_iff_ne_zero]; simp
    simp only [cball, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx he ⊢
    exact hx.trans ((le_inv_comm₀ he0 hs).1 he)
  refine hK.induction_on (p := fun K => ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹)
    (by simp) ?_ ?_ ?_
  · intro s t hst ht
    exact ht.mono fun e he => hst.trans he
  · intro s t hs ht
    filter_upwards [hs, ht] with e h1 h2 using Set.union_subset h1 h2
  · intro x _
    by_cases hx : x = 0
    · subst hx
      exact ⟨cball 1, mem_nhdsWithin_of_mem_nhds (cball_mem_nhds 1), key 1⟩
    · exact ⟨cball (Units.mk0 x hx), mem_nhdsWithin_of_mem_nhds
        ((isOpen_cball _).mem_nhds (by simp [cball])), key _⟩

variable {n n' : Type}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem withCol_add (x₀ : Matrix n n' k) (y z : n → k) :
    withCol x₀ (y + z) = withCol x₀ y + withCol (0 : Matrix n n' k) z := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [withCol]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_withCol_zero :
    Continuous fun z : n → k => withCol (0 : Matrix n n' k) z := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simp only [withCol, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

theorem eventually_box_subset [Fintype n] {ϖ : kˣ} (h : IsUnif ϖ) {U : Set (n → k)}
    (hU : U ∈ 𝓝 (0 : n → k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ z ∈ box n (ϖ ^ e), z ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose s hs using fun i => exists_cball_subset (ht i)
  filter_upwards [Filter.eventually_all.2 fun i => eventually_pow_le h (s i)] with e he z hz
  exact hsub fun i _ => hs i (le_trans (hz i) (he i))

theorem eventually_adapted [Fintype n] [Fintype n'] {ϖ : kˣ} (h : IsUnif ϖ)
    {Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ (x₀ : Matrix n n' k) (y : n → k),
      (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧
        ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  obtain ⟨Λ, hΛ, hinv⟩ := sb_matrix_exists_isOpen_addSubgroup k _ _ Ψ hΨ
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ r : n, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k => x (Sum.inl r) (Sum.inr 0)) ''
        tsupport Ψ ⊆ cball (ϖ ^ e)⁻¹ := fun r =>
    eventually_subset_cball h (hc.image (by fun_prop))
  have h0 : withCol (0 : Matrix n n' k) (0 : n → k) = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [withCol]
  have h2 : (fun z : n → k => withCol (0 : Matrix n n' k) z) ⁻¹' (Λ : Set _) ∈ 𝓝 (0 : n → k) :=
    (hΛ.preimage continuous_withCol_zero).mem_nhds (by
      simp only [Set.mem_preimage, h0]; exact Λ.zero_mem)
  filter_upwards [Filter.eventually_all.2 h1, eventually_box_subset h h2] with e he1 he2 x₀ y
  refine ⟨fun hne r => ?_, fun z hz => ?_⟩
  · exact he1 r ⟨withCol x₀ y, subset_tsupport _ hne, rfl⟩
  · rw [withCol_add]
    exact hinv _ _ (he2 z hz)

theorem exists_adapted_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  intro k _ _ _ _ n _ _ n' _ _ S hS hSB ϖ h
  exact ((Filter.eventually_ge_atTop 1).and ((Filter.eventually_all_finite hS).2
    fun Ψ hΨ => eventually_adapted h (hSB Ψ hΨ))).exists

end GlobalTheory.AdaptedExp
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.GenericLevel

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_residueChar {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ φ : AddChar 𝓀[k] Circle, ∀ x : 𝒪[k],
      φ (IsLocalRing.residue 𝒪[k] x) = ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) := by
  have hsurj : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  have h1 : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := by
    intro y hy
    exact (hψ 1).2 (by simp) y (by simpa using hy)
  have key : ∀ x y : 𝒪[k], IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y →
      ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) = ψ (((ϖ⁻¹ : kˣ) : k) * (y : k)) := by
    intro x y hxy
    have h2 := (hϖ _).1 ((residue_eq_iff_lt x y).1 hxy)
    have h0 : valuation k (ϖ : k) ≠ 0 := by simp
    have h3 : valuation k (((ϖ⁻¹ : kˣ) : k) * ((x : k) - (y : k))) ≤ 1 := by
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact (inv_mul_le_one₀ (zero_lt_iff.2 h0)).2 h2
    have h4 : ((ϖ⁻¹ : kˣ) : k) * (x : k)
        = ((ϖ⁻¹ : kˣ) : k) * (y : k) + ((ϖ⁻¹ : kˣ) : k) * ((x : k) - (y : k)) := by ring
    rw [h4, AddChar.map_add_eq_mul, h1 _ h3, mul_one]
  let f : 𝓀[k] → Circle := fun t => ψ (((ϖ⁻¹ : kˣ) : k) * ((Function.surjInv hsurj t : 𝒪[k]) : k))
  have hf : ∀ x : 𝒪[k], f (IsLocalRing.residue 𝒪[k] x) = ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) :=
    fun x => key _ _ (Function.surjInv_eq hsurj _)
  refine ⟨⟨f, ?_, ?_⟩, hf⟩
  · have := hf 0
    simpa using this
  · intro s t
    obtain ⟨x, rfl⟩ := hsurj s
    obtain ⟨y, rfl⟩ := hsurj t
    rw [← map_add (f := _), hf, hf, hf, ← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    ring

end

section
variable {F a : Type} [Field F] [Fintype a] [DecidableEq a]

def upperUnip (F : Type) {a : Type} [Field F] [Fintype a] [DecidableEq a] (pos : a → ℕ) :
    Subgroup (GL a F) where
  carrier := {g | IsUpperUnip pos (g : Matrix a a F)}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {g h} hg hh => Radical.Uni.mul (b := pos) hg hh
  inv_mem' := fun {g} hg => Radical.Uni.inv (b := pos) hg

theorem superSum_mul {pos : a → ℕ} {M M' : Matrix a a F} (h : IsUpperUnip pos M)
    (h' : IsUpperUnip pos M') : superSum pos (M * M') = superSum pos M + superSum pos M' := by
  unfold superSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · exact Radical.Uni.mul_apply_succ (b := pos) h h' hs
  · simp

omit [DecidableEq a] in
theorem superSum_map {R : Type} [CommRing R] (f : R →+* F) (pos : a → ℕ) (M : Matrix a a R) :
    superSum pos (M.map f) = f (∑ r, ∑ s, if pos s = pos r + 1 then M r s else 0) := by
  unfold superSum

  simp only [map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

noncomputable def genChar (φ : AddChar F Circle) (pos : a → ℕ) : upperUnip F pos →* ℂˣ :=
  Circle.toUnits.comp (MonoidHom.mk' (fun g => φ (superSum pos ((g : GL a F) : Matrix a a F)))
    (fun g h => by
      rw [← AddChar.map_add_eq_mul, ← superSum_mul g.2 h.2]
      rfl))

theorem genChar_apply (φ : AddChar F Circle) (pos : a → ℕ) (g : upperUnip F pos) :
    ((genChar φ pos g : ℂˣ) : ℂ) = φ (superSum pos ((g : GL a F) : Matrix a a F)) := rfl

end

theorem exists_isGenericLevel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ κ l : ℕ,
      ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsGenericLevel ψ ϖ P := by
  intro k _ _ _ _ ψ hψ ϖ hϖ κ l
  obtain ⟨φ, hφ⟩ := exists_residueChar hψ hϖ
  refine ⟨TypeDatum.ofResidue (upperUnip 𝓀[k] (framePos κ l)) (genChar φ (framePos κ l)), ?_, ?_⟩
  · intro g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, rfl, rfl⟩, hu⟩
    · rintro ⟨gb, ⟨u, rfl, rfl⟩, hu⟩
      exact ⟨u, hu, rfl⟩
  · rintro ⟨g, u, hu, rfl⟩
    have h := TypeDatum.ofResidue_lam (upperUnip 𝓀[k] (framePos κ l)) (genChar φ (framePos κ l)) u hu
    rw [h, genChar_apply]
    have e1 := superSum_map (IsLocalRing.residue 𝒪[k]) (framePos κ l) (u : Matrix _ _ 𝒪[k])
    have e2 := superSum_map (algebraMap 𝒪[k] k) (framePos κ l) (u : Matrix _ _ 𝒪[k])
    have e3 := hφ (∑ r, ∑ s, if framePos κ l s = framePos κ l r + 1
      then (u : Matrix _ _ 𝒪[k]) r s else 0)
    rw [← e1] at e3
    have e4 : φ (superSum (framePos κ l) ((u : Matrix _ _ 𝒪[k]).map (IsLocalRing.residue 𝒪[k])))
        = ψ (((ϖ⁻¹ : kˣ) : k) *
          superSum (framePos κ l) ((u : Matrix _ _ 𝒪[k]).map (algebraMap 𝒪[k] k))) := by
      rw [e3, e2]
      rfl
    exact congrArg (fun z : Circle => (z : ℂ)) e4

end GlobalTheory.GenericLevel
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.CosetFn
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem deltaR_mul (g g' : GL n k) : deltaR c (g * g') = deltaR c g * deltaR c g' := by
  simp only [deltaR, nabs, map_mul, NNReal.coe_mul, mul_zpow]

theorem deltaR_one : deltaR c (1 : GL n k) = 1 := by
  simp [deltaR, nabs]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mul_embX_mem_R {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (g : GL n k) :
    u * embX c g ∈ R k n c 1 :=
  mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩)

theorem deltaR_eq {J : Subgroup (GL (n ⊕ Fin c) k)} {h : GL (n ⊕ Fin c) k}
    (H : ∀ g ∈ prX (Cgrp J h), deltaR c g = 1) {u u' j j' : GL (n ⊕ Fin c) k} {g g' : GL n k}
    (hu : u ∈ N k n c 1) (hu' : u' ∈ N k n c 1) (hj : j ∈ J) (hj' : j' ∈ J)
    (e : u * embX c g * h * j = u' * embX c g' * h * j') : deltaR c g = deltaR c g' := by
  have h1 : g'⁻¹ * g ∈ prX (Cgrp J h) := by
    refine ⟨embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹,
      Radical.conj_mem _ (mul_mem (inv_mem hu') hu), ?_⟩
    have e2 : embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹ * embX c (g'⁻¹ * g)
        = (u' * embX c g')⁻¹ * (u * embX c g) := by
      simp only [map_mul, map_inv]; group
    rw [e2]
    refine Subgroup.mem_inf.2
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (mul_embX_mem_R hu' g')) (mul_embX_mem_R hu g), ?_⟩
    have e3 : u * embX c g = u' * embX c g' * h * j' * j⁻¹ * h⁻¹ := by
      rw [← e]; group
    have e4 : h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ = j' * j⁻¹ := by
      rw [e3]; group
    show h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ ∈ J
    rw [e4]
    exact mul_mem hj' (inv_mem hj)
  have h2 := deltaR_mul (c := c) g' (g'⁻¹ * g)
  rw [H _ h1, mul_inv_cancel_left, mul_one] at h2
  exact h2

end

theorem exists_isCosetFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k)
    (H : ∀ g ∈ prX (Cgrp J h), deltaR c g = 1) : ∃ f, IsCosetFn J h f ∧ f h = 1 := by
  classical
  let P : GL (n ⊕ Fin c) k → GL n k → Prop := fun x g =>
    ∃ u ∈ N k n c 1, ∃ j ∈ J, x = u * embX c g * h * j
  let f : GL (n ⊕ Fin c) k → ℂ := fun x =>
    if hx : ∃ g, P x g then (deltaR c hx.choose : ℂ) else 0
  have fpos : ∀ x g, P x g → f x = (deltaR c g : ℂ) := by
    intro x g hg
    have hx : ∃ g, P x g := ⟨g, hg⟩
    obtain ⟨u, hu, j, hj, e⟩ := hx.choose_spec
    obtain ⟨u', hu', j', hj', e'⟩ := hg
    simp only [f, dif_pos hx]
    rw [deltaR_eq H hu hu' hj hj' (e.symm.trans e')]
  have fneg : ∀ x, (¬ ∃ g, P x g) → f x = 0 := fun x hx => by simp only [f, dif_neg hx]
  have left : ∀ u ∈ N k n c 1, ∀ (g g' : GL n k) x, P x g' → P (u * embX c g * x) (g * g') := by
    rintro u hu g g' x ⟨u', hu', j, hj, rfl⟩
    refine ⟨u * (embX c g * u' * (embX c g)⁻¹), mul_mem hu (Radical.conj_mem _ hu'), j, hj, ?_⟩
    simp only [map_mul]; group
  have right : ∀ j ∈ J, ∀ g x, P x g → P (x * j) g := by
    rintro j hj g x ⟨u', hu', j', hj', rfl⟩
    exact ⟨u', hu', j' * j, mul_mem hj' hj, by group⟩
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro u hu g x
    by_cases hx : ∃ g', P x g'
    · obtain ⟨g', hg'⟩ := hx
      rw [fpos _ _ (left u hu g g' x hg'), fpos _ _ hg', deltaR_mul]
      push_cast; rfl
    · rw [fneg x hx, mul_zero]
      apply fneg
      rintro ⟨g', hg'⟩
      apply hx
      have := left _ (Radical.conj_mem g⁻¹ (inv_mem hu)) g⁻¹ g' _ hg'
      have e : embX c g⁻¹ * u⁻¹ * (embX c g⁻¹)⁻¹ * embX c g⁻¹ * (u * embX c g * x) = x := by
        simp only [map_inv]; group
      rw [e] at this
      exact ⟨_, this⟩
  · intro x j hj
    by_cases hx : ∃ g', P x g'
    · obtain ⟨g', hg'⟩ := hx
      rw [fpos _ _ (right j hj g' x hg'), fpos _ _ hg']
    · rw [fneg x hx]
      apply fneg
      rintro ⟨g', hg'⟩
      apply hx
      have := right _ (inv_mem hj) g' _ hg'
      rw [mul_inv_cancel_right] at this
      exact ⟨_, this⟩
  · intro x hx
    apply fneg
    rintro ⟨g, u, hu, j, hj, e⟩
    apply hx
    symm
    rw [DoubleCoset.eq]
    exact ⟨_, mul_embX_mem_R hu g, j, hj, e⟩
  · rw [fpos h 1 ⟨1, one_mem _, 1, one_mem _, by simp⟩, deltaR_one]
    simp

end GlobalTheory.CosetFn
end

section

open scoped Matrix

namespace GlobalTheory.UTrans.CharDet

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem isU_one : IsU σ G 1 := fun x y => by simp

theorem isU_refl (hG : IsHerm σ G) {x : Fin n → E} {u : E} (hx : hf σ G x x ≠ 0) (hu : u * σ u = 1) :
    IsU σ G (tv σ G x ((u - 1) / hf σ G x x)) := by
  apply Calc.isU_tv σ G hG.invol hG.herm
  rw [map_div₀, Calc.hf_conj σ G hG.invol hG.herm, map_sub, map_one]
  field_simp
  linear_combination hu

theorem refl_mul {x : Fin n → E} (u v : E) (hx : hf σ G x x ≠ 0) :
    tv σ G x ((u - 1) / hf σ G x x) * tv σ G x ((v - 1) / hf σ G x x) =
      tv σ G x ((u * v - 1) / hf σ G x x) := by
  rw [Calc.tv_mul]
  congr 1
  field_simp
  ring

theorem refl_det {x : Fin n → E} (u : E) (hx : hf σ G x x ≠ 0) :
    (tv σ G x ((u - 1) / hf σ G x x)).det = u := by
  rw [Calc.tv_det]
  field_simp
  ring

theorem refl_one (x : Fin n → E) : tv σ G x ((1 - 1) / hf σ G x x) = 1 := by
  ext a b
  simp [tv]

variable [CharZero E] {A : Type} [CommGroup A] {X : Matrix (Fin n) (Fin n) E → A}

theorem char_refl_eq (hG : IsHerm σ G)
    (h : (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) ∨ ∀ x y : Fin n → E, hf σ G x x ≠ 0 → hf σ G y y ≠ 0 →
      ∃ a : E, hf σ G y y = σ a * a * hf σ G x x)
    (hX : ∀ a b, IsU σ G a → IsU σ G b → X (a * b) = X a * X b)
    {x y : Fin n → E} {u : E} (hx : hf σ G x x ≠ 0) (hy : hf σ G y y ≠ 0) (hu : u * σ u = 1) :
    X (tv σ G x ((u - 1) / hf σ G x x)) = X (tv σ G y ((u - 1) / hf σ G y y)) := by
  rcases h with h | h
  · obtain ⟨m, hm, e⟩ := quasiReflection_eq_tvGen_mul E n σ G hG h x y u hx hy hu
    rw [e, hX _ _ ((tvGen_normal E n σ G hG).2 m hm).1 (isU_refl hG hy hu),
      GlobalTheory.T.unitaryCharacter_kills_unitaryTransvections E n σ G hG A X hX m hm, one_mul]
  · obtain ⟨a, ha⟩ := h x y hx hy
    have h1 : hf σ G (a • x) (a • x) = hf σ G y y := by
      rw [Calc.hf_smul_left, Calc.hf_smul_right, ha]; ring
    obtain ⟨γ, hγ, e⟩ := (GlobalTheory.T.unitary_generated_by_quasiReflections_and_witt E n σ G hG).2 y (a • x) hy h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
      exact hy ha
    have ha1 : σ a ≠ 0 := (map_ne_zero σ).2 ha0
    have h2 : tv σ G x ((u - 1) / hf σ G x x) = tv σ G (a • x) ((u - 1) / hf σ G y y) := by
      rw [Calc.tv_smul, ha]
      congr 1
      field_simp
    have h3 : γ * tv σ G x ((u - 1) / hf σ G x x) = tv σ G y ((u - 1) / hf σ G y y) * γ := by
      rw [h2, Calc.conj_tv σ G γ _ _ hγ, e]
    have h4 := congrArg X h3
    rw [hX _ _ hγ (isU_refl hG hx hu), hX _ _ (isU_refl hG hy hu) hγ, mul_comm] at h4
    exact mul_right_cancel h4

theorem char_prod (hG : IsHerm σ G)
    (h : (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) ∨ ∀ x y : Fin n → E, hf σ G x x ≠ 0 → hf σ G y y ≠ 0 →
      ∃ a : E, hf σ G y y = σ a * a * hf σ G x x)
    (hX : ∀ a b, IsU σ G a → IsU σ G b → X (a * b) = X a * X b)
    {x : Fin n → E} (hx : hf σ G x x ≠ 0) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    IsU σ G (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod ∧
      X (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod =
        X (tv σ G x (((l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod.det - 1) / hf σ G x x)) := by
  induction l with
  | nil => exact ⟨isU_one, by simp only [List.map_nil, List.prod_nil, Matrix.det_one, refl_one]⟩
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨hp, hv⟩ := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons]
    refine ⟨Calc.isU_mul σ G _ _ (isU_refl hG hp hv) h1, ?_⟩
    rw [hX _ _ (isU_refl hG hp hv) h1, h2, char_refl_eq hG h hX hp hx hv, Matrix.det_mul, refl_det _ hp,
      ← refl_mul _ _ hx, hX _ _ (isU_refl hG hx hv) (isU_refl hG hx (h1.det_mul_conj_det hG.det_ne))]

end GlobalTheory.UTrans.CharDet

theorem GlobalTheory.UTrans.char_eq_one_of_det_eq_one : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ((∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0) ∨ ∀ x y : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G y y ≠ 0 → ∃ a : E, GlobalTheory.UTrans.hf σ G y y = σ a * a * GlobalTheory.UTrans.hf σ G x x) → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ γ, GlobalTheory.UTrans.IsU σ G γ → γ.det = 1 → X γ = 1 := by
  intro E _ _ n σ G hG h A _ X hX γ hγ hd
  have h1 : X 1 = 1 := by
    have := hX 1 1 CharDet.isU_one CharDet.isU_one
    rw [mul_one] at this
    exact left_eq_mul.1 this
  obtain ⟨l, hl, e⟩ := (GlobalTheory.T.unitary_generated_by_quasiReflections_and_witt E n σ G hG).1 γ hγ
  cases l with
  | nil => rw [e]; simpa using h1
  | cons p l =>
    have h2 := (CharDet.char_prod hG h hX (hl p List.mem_cons_self).1 _ hl).2
    rw [← e, hd, CharDet.refl_one] at h2
    rw [h2, h1]
end

section

open Formalism.REAL Finset

theorem _root_.GlobalTheory.T.traced_qminor_comatrix_truncated_inverse : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (N : ℕ), algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
  first | exact @GlobalTheory.TracedComatrix.traced_comatrix | exact GlobalTheory.TracedComatrix.traced_comatrix | (intros; apply GlobalTheory.TracedComatrix.traced_comatrix <;> assumption)
end
