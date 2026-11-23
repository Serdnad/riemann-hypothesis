module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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

@[expose] public section

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

private theorem chi_orth {Q : Type} [Group Q] [Fintype Q] (f g : Q →* ℂˣ) (h : f ≠ g) :
    ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ g y := by
    by_contra hne
    push_neg at hne
    exact h (MonoidHom.ext hne)
  have ha : ((f y)⁻¹ * g y : ℂˣ) ≠ 1 := by
    intro h1
    exact hy (inv_mul_eq_one.mp h1)
  have ha' : ((((f y)⁻¹ * g y : ℂˣ)) : ℂ) ≠ 1 := by
    intro h1
    exact ha (Units.val_eq_one.mp h1)
  have key : ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ)
      = ((((f y)⁻¹ * g y : ℂˣ)) : ℂ) * ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft y)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_mulLeft, map_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : (((((f y)⁻¹ * g y : ℂˣ)) : ℂ) - 1) * ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) = 0 := by
    linear_combination -key
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) ha'
  · exact h3

private theorem c_conv {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (χ : I → Q →* ℂˣ) (hχ : Function.Injective χ) (c : Q → ℤ)
    (hc : ∀ x, (c x : ℂ) = ∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) (w : Q) :
    ∑ x, c x * c (x⁻¹ * w) = (Fintype.card Q : ℤ) * c w := by
  classical
  have hQ : ∀ t s : I, ∑ x, (((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)
      = if t = s then (Fintype.card Q : ℂ) else 0 := by
    intro t s
    split_ifs with hts
    · subst hts
      simp
    · exact chi_orth _ _ (fun e => hts (hχ e))
  have term : ∀ (x : Q) (t s : I), (((χ t x)⁻¹ : ℂˣ) : ℂ) * (((χ s (x⁻¹ * w))⁻¹ : ℂˣ) : ℂ)
      = (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) := by
    intro x t s
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul]
    ring
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, hc]
  calc ∑ x, (∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) * ∑ s, (((χ s (x⁻¹ * w))⁻¹ : ℂˣ) : ℂ)
      = ∑ x, ∑ t, ∑ s, (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => term x t s
    _ = ∑ t, ∑ s, ∑ x, (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ => Finset.sum_comm)
    _ = ∑ t, ∑ s, (((χ s w)⁻¹ : ℂˣ) : ℂ) * (if t = s then (Fintype.card Q : ℂ) else 0) := by
        simp only [← Finset.mul_sum, hQ]
    _ = (Fintype.card Q : ℂ) * ∑ t, (((χ t w)⁻¹ : ℂˣ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

private theorem opE_sum {G R W Q : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W]
    [Fintype Q] (ρ : Representation R G W) (g : Q → G) (c : Q → ℤ) :
    opE ρ (∑ x, Finsupp.single (g x) (c x)) = ∑ x, c x • ρ (g x) := by
  show (∑ x, Finsupp.single (g x) (c x)).sum (fun h n => n • ρ h) = _
  rw [← Finsupp.sum_finsetSum_index (fun a => zero_smul ℤ (ρ a)) (fun a m n => add_smul m n (ρ a))]
  exact Finset.sum_congr rfl fun x _ => Finsupp.sum_single_index (zero_smul ℤ (ρ (g x)))

theorem UpperTheory.mem_fixed_of_character_sum_projection :
    ∀ {G Q A I : Type} [Group G] [Group Q] [Fintype Q] [Group A] [Fintype I]
        (K : Subgroup G) (ι : A →* G) (π : A →* Q) (s : Q → A), (∀ x, π (s x) = x) →
        (∀ a, π a = 1 ↔ ι a ∈ K) → (∀ a, ∀ u ∈ K, (ι a)⁻¹ * u * ι a ∈ K) →
        ∀ (χ : I → Q →* ℂˣ), Function.Injective χ → ∀ (c : Q → ℤ),
        (∀ x, (c x : ℂ) = ∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) → ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) (v : W), v ∈ fixd ρ K →
        opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) (opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) v) =
          Fintype.card Q • opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) v := by
  intro G Q A I _ _ _ _ _ K ι π s hs hker _ χ hχ c hc R W _ _ _ ρ v hv
  have hv' : ∀ u ∈ K, ρ u v = v := hv
  have hT : ∀ y x, ρ (ι (s y)) (ρ (ι (s x)) v) = ρ (ι (s (y * x))) v := by
    intro y x
    have hk : ι ((s (y * x))⁻¹ * (s y * s x)) ∈ K := by
      rw [← hker]
      simp [map_mul, map_inv, hs]
    calc ρ (ι (s y)) (ρ (ι (s x)) v) = ρ (ι (s y * s x)) v := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ (ι (s (y * x) * ((s (y * x))⁻¹ * (s y * s x)))) v := by rw [mul_inv_cancel_left]
      _ = ρ (ι (s (y * x))) v := by
          rw [map_mul ι, map_mul ρ, Module.End.mul_apply, hv' _ hk]
  have hE : opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) = ∑ x, c x • ρ (ι (s x)) :=
    opE_sum ρ (fun x => ι (s x)) c
  rw [hE]

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, hT]
  calc ∑ a, ∑ b, (c a * c b) • ρ (ι (s (b * a))) v
      = ∑ b, ∑ a, (c a * c b) • ρ (ι (s (b * a))) v := Finset.sum_comm
    _ = ∑ b, ∑ z, (c b * c (b⁻¹ * z)) • ρ (ι (s z)) v := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft b⁻¹)]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [Equiv.coe_mulLeft, mul_inv_cancel_left]
        rw [mul_comm (c (b⁻¹ * z))]
    _ = ∑ z, (∑ b, c b * c (b⁻¹ * z)) • ρ (ι (s z)) v := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_smul]
    _ = ∑ z, Fintype.card Q • c z • ρ (ι (s z)) v := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [c_conv χ hχ c hc z, mul_smul, natCast_zsmul]
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

private theorem sep_char {A : Type} [AddCommGroup A] (H : AddSubgroup A) {a : A} (ha : a ∉ H) :
    ∃ ψ : AddChar A Circle, (∀ u ∈ H, ψ u = 1) ∧ ψ a ≠ 1 := by
  have hne : (a : A ⧸ H) ≠ 0 := fun h => ha ((QuotientAddGroup.eq_zero_iff _).1 h)
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let e : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro _ ⟨m, rfl⟩
      exact ⟨m, by simp⟩)
  have he : ∀ b, e b = 0 → b = 0 := by
    intro b
    induction b using QuotientAddGroup.induction_on with
    | H q =>
      intro h
      have h1 : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
      rw [AddCircle.coe_eq_zero_iff] at h1 ⊢
      obtain ⟨m, hm⟩ := h1
      refine ⟨m, ?_⟩
      have h2 : ((m : ℚ) : ℝ) = q := by simpa using hm
      have h3 : (m : ℚ) = q := by exact_mod_cast h2
      simpa using h3
  let f : A →+ AddCircle (1 : ℝ) := e.comp (AddMonoidHom.comp (χ : A ⧸ H →+ AddCircle (1 : ℚ)) (QuotientAddGroup.mk' H))
  let ψ : AddChar A Circle :=
    { toFun := fun x => AddCircle.toCircle (f x)
      map_zero_eq_one' := by rw [map_zero, AddCircle.toCircle_zero]
      map_add_eq_mul' := fun x y => by rw [map_add (f := _), AddCircle.toCircle_add] }
  refine ⟨ψ, fun u hu => ?_, fun h => ?_⟩
  · have h0 : f u = 0 := by
      have : QuotientAddGroup.mk' H u = 0 := (QuotientAddGroup.eq_zero_iff _).2 hu
      show e (χ (QuotientAddGroup.mk' H u)) = 0
      rw [this, map_zero, map_zero]
    show AddCircle.toCircle (f u) = 1
    rw [h0, AddCircle.toCircle_zero]
  · have h2 : AddCircle.toCircle (f a) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h
    exact hχ (he _ (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero h2))

private theorem cont_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    (H : AddSubgroup A) (hH : IsOpen (H : Set A)) (ψ : AddChar A Circle) (h : ∀ u ∈ H, ψ u = 1) :
    Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' (H : Set A), hH.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · simp [H.zero_mem]
  · intro y hy
    have h1 : ψ (y - x) = 1 := h _ hy
    have h2 : y = (y - x) + x := by abel
    rw [h2, AddChar.map_add_eq_mul, h1, one_mul]

theorem UpperTheory.exists_level_one_addChar_lifting_residue :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
        ∃ (ψ : AddChar k Circle) (φ : AddChar 𝓀[k] Circle), Lev1 ψ ∧ φ ≠ 1 ∧ ∀ y : 𝒪[k], ψ (y : k) = φ (IsLocalRing.residue 𝒪[k] y) := by
  intro k _ _ _ _
  let M : AddSubgroup k :=
    { carrier := {x | valuation k x < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => lt_of_le_of_lt ((valuation k).map_add a b) (max_lt ha hb)
      neg_mem' := fun {a} ha => by
        show valuation k (-a) < 1
        rw [Valuation.map_neg]; exact ha }
  have hMo : IsOpen (M : Set k) := by
    have h := Valuation.isOpen_ball (v := valuation k) 1
    convert h using 1
    ext x
    exact ((valuation k).restrict_lt_one_iff (x := x)).symm
  have h1M : (1 : k) ∉ M := by
    intro h
    have h' : valuation k (1 : k) < 1 := h
    simp at h'
  obtain ⟨ψ, hψM, hψ1⟩ := sep_char M h1M
  have hres : ∀ y z : 𝒪[k], IsLocalRing.residue 𝒪[k] y = IsLocalRing.residue 𝒪[k] z → ψ (y : k) = ψ (z : k) := by
    intro y z h
    have h0 : IsLocalRing.residue 𝒪[k] (y - z) = 0 := by rw [map_sub, h, sub_self]
    have h1 : ψ ((y - z : 𝒪[k]) : k) = 1 := hψM _ ((GlobalTheory.StepData.residue_eq_zero_iff_lt _).1 h0)
    have h2 : (y : k) = ((y - z : 𝒪[k]) : k) + (z : k) := by push_cast; abel
    rw [h2, AddChar.map_add_eq_mul, h1, one_mul]
  have hsurj := IsLocalRing.residue_surjective (R := 𝒪[k])
  let σ : 𝓀[k] → 𝒪[k] := Function.surjInv hsurj
  have hσ : ∀ c, IsLocalRing.residue 𝒪[k] (σ c) = c := Function.surjInv_eq hsurj
  let φ : AddChar 𝓀[k] Circle :=
    { toFun := fun c => ψ (σ c : k)
      map_zero_eq_one' := by
        have : ψ (σ 0 : k) = ψ ((0 : 𝒪[k]) : k) := hres _ _ (by rw [hσ, map_zero])
        rw [this]; simp
      map_add_eq_mul' := fun c d => by
        have : ψ (σ (c + d) : k) = ψ ((σ c + σ d : 𝒪[k]) : k) := hres _ _ (by rw [hσ, map_add (f := _), hσ, hσ])
        rw [this]; push_cast; rw [AddChar.map_add_eq_mul] }
  have hφ : ∀ y : 𝒪[k], ψ (y : k) = φ (IsLocalRing.residue 𝒪[k] y) := fun y =>
    hres _ _ (hσ _).symm
  refine ⟨ψ, φ, ⟨cont_char M hMo ψ hψM, hψM, 1, by simp, hψ1⟩, fun h => hψ1 ?_, hφ⟩
  have h2 := hφ 1
  rw [h] at h2
  simpa using h2
end
