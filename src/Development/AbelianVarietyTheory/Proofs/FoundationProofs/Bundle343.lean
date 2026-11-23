module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
public import ReciprocityTheory.GaloisValuations.Bundle002
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.Ord2.OpenInv

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_trans {n : ℕ} {a b c : Qbar l} (h1 : Cg n a b) (h2 : Cg n b c) : Cg n a c := by
  unfold Cg at *
  calc ‖a - c‖ = ‖(a - b) + (b - c)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖a - b‖ ‖b - c‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h1 h2

theorem cg_symm {n : ℕ} {a b : Qbar l} (h1 : Cg n a b) : Cg n b a := by
  unfold Cg at *
  rwa [norm_sub_rev]

theorem cg_refl {n : ℕ} (a : Qbar l) : Cg n a a := by
  unfold Cg
  rw [sub_self, norm_zero]
  exact norm_nonneg _

private theorem eps_eq_algebraMap_cycZ (s : G ℚ Ω) :
    eps l s = algebraMap ℚ_[l] (Qbar l) ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]) : ℚ_[l]) := by
  unfold eps cycBar
  rfl

theorem norm_eps_le (s : G ℚ Ω) : ‖eps l s‖ ≤ 1 := by
  rw [eps_eq_algebraMap_cycZ]
  unfold Qbar
  rw [PadicAlgCl.norm_extends]
  exact (ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]).2

theorem cg_mul_eps {n : ℕ} (s : G ℚ Ω) {a b : Qbar l} (h : Cg n a b) : Cg n (eps l s * a) (eps l s * b) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖eps l s‖ * ‖a - b‖ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right (norm_eps_le s) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h

theorem eps_mul (s t : G ℚ Ω) : eps l (s * t) = eps l s * eps l t := by
  unfold eps
  rw [map_mul, Units.val_mul]

theorem eps_one : eps l (1 : G ℚ Ω) = 1 := by
  unfold eps
  rw [map_one, Units.val_one]

theorem pow_pos' (n : ℕ) : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ :=
  norm_pos_iff.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero))

private theorem continuous_eps' : Continuous (fun s : G ℚ Ω => eps l s) := by
  have h : (fun s : G ℚ Ω => eps l s) =
      fun s => algebraMap ℚ_[l] (Qbar l) ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]) : ℚ_[l]) := by
    funext s
    exact eps_eq_algebraMap_cycZ s
  rw [h]
  have h1 : Continuous fun s : G ℚ Ω => ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (ReciprocityTheory.Gal.continuous_cycZ ℚ Ω l)
  have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (h2.comp h1)

theorem ev_cg {X : Type} [TopologicalSpace X] {n : ℕ} {f g : X → Qbar l} (hf : Continuous f) (hg : Continuous g)
    {x : X} (h : f x = g x) : ∀ᶠ y in 𝓝 x, Cg n (f y) (g y) := by
  have hc : Continuous fun y => ‖f y - g y‖ := (hf.sub hg).norm
  have h0 : ‖f x - g x‖ < ‖((l : ℕ) : Qbar l) ^ n‖ := by
    rw [h, sub_self, norm_zero]
    exact pow_pos' n
  filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h0] with y hy
  unfold Cg
  exact hy.le

def invSub (n : ℕ) (H : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) : Subgroup (G ℚ Ω) where
  carrier := {k | k ∈ H ∧ Cg n (eps l k) 1 ∧ ∀ s ∈ H, ∀ t ∈ H, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)}
  one_mem' := ⟨H.one_mem, by rw [eps_one]; exact cg_refl _, fun s _ t _ => by
    rw [mul_one, mul_one]; exact ⟨cg_refl _, cg_refl _⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨H.mul_mem ha hb, ?_, fun s hs t ht => ⟨?_, ?_⟩⟩
    · rw [eps_mul]
      have := cg_mul_eps a hb1
      rw [mul_one] at this
      exact cg_trans this ha1
    · rw [← mul_assoc]
      exact cg_trans (hb2 _ (H.mul_mem hs ha) t ht).1 (ha2 s hs t ht).1
    · rw [← mul_assoc]
      exact cg_trans (hb2 s hs _ (H.mul_mem ht ha)).2 (ha2 s hs t ht).2
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨H.inv_mem ha, ?_, fun s hs t ht => ⟨?_, ?_⟩⟩
    · have := cg_mul_eps a⁻¹ ha1
      rw [mul_one, ← eps_mul, inv_mul_cancel, eps_one] at this
      exact cg_symm this
    · have := (ha2 _ (H.mul_mem hs (H.inv_mem ha)) t ht).1
      rw [inv_mul_cancel_right] at this
      exact cg_symm this
    · have := (ha2 s hs _ (H.mul_mem ht (H.inv_mem ha))).2
      rw [inv_mul_cancel_right] at this
      exact cg_symm this

theorem open_inv : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (H I : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), IsClosed (H : Set (G ℚ Ω)) → I ≤ H → ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => ξ p.1 p.2) ((H : Set (G ℚ Ω)) ×ˢ (H : Set (G ℚ Ω))) → (∀ i ∈ I, eps l i = 1) → (∀ s ∈ H, ∀ t ∈ H, ∀ i ∈ I, Cg n (ξ (s * i) t) (ξ s t) ∧ Cg n (ξ s (t * i)) (ξ s t)) → ∃ K : Subgroup (G ℚ Ω), I ≤ K ∧ K ≤ H ∧ IsOpen ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) ∧ (∀ k ∈ K, Cg n (eps l k) 1) ∧ ∀ s ∈ H, ∀ t ∈ H, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t) := by
  intro l _ Ω _ _ _ n H I ξ hH hIH hξ hI hinv
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  have hξc : Continuous fun p : H × H => ξ p.1 p.2 := by
    have hp : Continuous fun p : H × H => ((p.1 : G ℚ Ω), (p.2 : G ℚ Ω)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    exact hξ.comp_continuous hp (fun p => ⟨p.1.2, p.2.2⟩)
  have hL : ∀ᶠ k in 𝓝 (1 : H), ∀ y ∈ (Set.univ : Set (H × H)),
      Cg n (ξ ((y.1 * k : H) : G ℚ Ω) y.2) (ξ y.1 y.2) := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun y _ => ?_
    exact ev_cg (X := H × (H × H)) (n := n)
      (f := fun z => ξ ((z.2.1 * z.1 : H) : G ℚ Ω) z.2.2) (g := fun z => ξ z.2.1 z.2.2)
      (hξc.comp ((continuous_snd.fst.mul continuous_fst).prodMk continuous_snd.snd))
      (hξc.comp (continuous_snd.fst.prodMk continuous_snd.snd))
      (x := ((1 : H), y)) (by simp)
  have hR : ∀ᶠ k in 𝓝 (1 : H), ∀ y ∈ (Set.univ : Set (H × H)),
      Cg n (ξ y.1 ((y.2 * k : H) : G ℚ Ω)) (ξ y.1 y.2) := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun y _ => ?_
    exact ev_cg (X := H × (H × H)) (n := n)
      (f := fun z => ξ z.2.1 ((z.2.2 * z.1 : H) : G ℚ Ω)) (g := fun z => ξ z.2.1 z.2.2)
      (hξc.comp (continuous_snd.fst.prodMk (continuous_snd.snd.mul continuous_fst)))
      (hξc.comp (continuous_snd.fst.prodMk continuous_snd.snd))
      (x := ((1 : H), y)) (by simp)
  have hE : ∀ᶠ k : H in 𝓝 (1 : H), Cg n (eps l (k : G ℚ Ω)) 1 := by
    refine ev_cg (X := H) (n := n) (f := fun k => eps l (k : G ℚ Ω)) (g := fun _ => 1)
      (continuous_eps'.comp continuous_subtype_val) continuous_const ?_
    show eps l ((1 : H) : G ℚ Ω) = 1
    rw [OneMemClass.coe_one, eps_one]
  refine ⟨invSub n H ξ, ?_, fun k hk => hk.1, ?_, fun k hk => hk.2.1, fun s hs t ht k hk => hk.2.2 s hs t ht⟩
  · intro i hi
    have hiH : i ∈ H := hIH hi
    show i ∈ H ∧ Cg n (eps l i) 1 ∧ ∀ s ∈ H, ∀ t ∈ H, Cg n (ξ (s * i) t) (ξ s t) ∧ Cg n (ξ s (t * i)) (ξ s t)
    refine ⟨hiH, ?_, fun s hs t ht => hinv s hs t ht i hi⟩
    rw [hI i hi]
    exact cg_refl _
  · apply Subgroup.isOpen_of_mem_nhds (g := 1)
    filter_upwards [hL, hR, hE] with k hkL hkR hkE
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    show (k : G ℚ Ω) ∈ H ∧ Cg n (eps l (k : G ℚ Ω)) 1 ∧ ∀ s ∈ H, ∀ t ∈ H,
      Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)
    exact ⟨k.2, hkE, fun s hs t ht => ⟨hkL (⟨s, hs⟩, ⟨t, ht⟩) trivial, hkR (⟨s, hs⟩, ⟨t, ht⟩) trivial⟩⟩

end GlobalTheory.Ord2.OpenInv

end
end

section

noncomputable section

open scoped Matrix

namespace GlobalTheory.CommutingExistence

variable {k : Type} [Field k]

theorem trace_two (A : Matrix (Fin 2) (Fin 2) k) (h1 : A.det = 1) (h2 : (A - 1).det = 0) :
    A 0 0 + A 1 1 = 2 := by
  rw [Matrix.det_fin_two] at h1 h2
  simp at h2
  linear_combination h1 - h2

theorem mul_nil (A B : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1) (hB : B.det = 1)
    (hA' : (A - 1).det = 0) (hB' : (B - 1).det = 0) (hAB : (A * B - 1).det = 0) :
    (A - 1) * (B - 1) = 0 := by
  have tA := trace_two A hA hA'
  have tB := trace_two B hB hB'
  have tAB := trace_two (A * B) (by rw [Matrix.det_mul, hA, hB, mul_one]) hAB
  rw [Matrix.det_fin_two] at hA hB
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at tAB
  obtain ⟨x, hx⟩ : ∃ x, A 0 0 = 1 + x := ⟨A 0 0 - 1, by ring⟩
  obtain ⟨a, ha⟩ : ∃ a, B 0 0 = 1 + a := ⟨B 0 0 - 1, by ring⟩
  have hx' : A 1 1 = 1 - x := by linear_combination tA - hx
  have ha' : B 1 1 = 1 - a := by linear_combination tB - ha
  rw [hx, hx'] at hA tAB
  rw [ha, ha'] at hB tAB
  have e1 : x ^ 2 + A 0 1 * A 1 0 = 0 := by linear_combination -hA
  have e2 : a ^ 2 + B 0 1 * B 1 0 = 0 := by linear_combination -hB
  have e3 : 2 * x * a + A 0 1 * B 1 0 + A 1 0 * B 0 1 = 0 := by linear_combination tAB
  have f00 : x * a + A 0 1 * B 1 0 = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination a ^ 2 * e1 - A 0 1 * A 1 0 * e2 + A 0 1 * B 1 0 * e3
  have f01 : x * B 0 1 - A 0 1 * a = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination B 0 1 ^ 2 * e1 + A 0 1 ^ 2 * e2 - A 0 1 * B 0 1 * e3
  have f10 : A 1 0 * a - x * B 1 0 = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination B 1 0 ^ 2 * e1 + A 1 0 ^ 2 * e2 - A 1 0 * B 1 0 * e3
  have f11 : A 1 0 * B 0 1 + x * a = 0 := by
    linear_combination e3 - f00
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hx', ha, ha']
  · linear_combination f00
  · linear_combination f01
  · linear_combination f10
  · linear_combination f11

theorem exists_comm [IsAlgClosed k] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) k) (H : Subgroup Γ)
    (hdet : ∀ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) k).det = 1)
    (hirr : ∀ V : Submodule k (Fin 2 → k),
      (∀ g ∈ H, ∀ v ∈ V, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) :
    ∃ φ ∈ ⁅H, H⁆, ((ρ φ : Matrix (Fin 2) (Fin 2) k) - 1).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : ⁅H, H⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hconj : ∀ g ∈ H, ∀ φ ∈ ⁅H, H⁆, g⁻¹ * φ * g ∈ ⁅H, H⁆ := by
    intro g hg φ hφ
    have := Subgroup.commutator_mem_commutator (H.inv_mem hg) (hle hφ)
    have h2 := Subgroup.mul_mem _ this hφ
    convert h2 using 1
    rw [commutatorElement_def]
    group
  let F : Submodule k (Fin 2 → k) :=
    { carrier := {v | ∀ φ ∈ ⁅H, H⁆, (ρ φ : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v}
      add_mem' := by
        intro a b ha hb φ hφ
        rw [Matrix.mulVec_add, ha φ hφ, hb φ hφ]
      zero_mem' := by
        intro φ _
        simp
      smul_mem' := by
        intro c a ha φ hφ
        rw [Matrix.mulVec_smul, ha φ hφ] }
  have hF : ∀ v, v ∈ F ↔ ∀ φ ∈ ⁅H, H⁆, (ρ φ : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v := fun _ => Iff.rfl
  have hFinv : ∀ g ∈ H, ∀ v ∈ F, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ F := by
    intro g hg v hv
    rw [hF] at hv ⊢
    intro φ hφ
    have h1 := hv _ (hconj g hg φ hφ)
    have h2 : φ * g = g * (g⁻¹ * φ * g) := by group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, h2, map_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, h1]
  have hFtop : ∀ v, v ∈ F := by
    rcases hirr F hFinv with h | h
    · intro w
      rw [hF]
      intro ψ hψ
      have : ((ρ ψ : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ w ∈ F := by
        rw [hF]
        intro φ hφ
        have h0 := mul_nil (ρ φ : Matrix (Fin 2) (Fin 2) k) (ρ ψ : Matrix (Fin 2) (Fin 2) k)
          (hdet _ (hle hφ)) (hdet _ (hle hψ)) (hcon _ hφ) (hcon _ hψ)
          (by rw [← Units.val_mul, ← map_mul]; exact hcon _ (Subgroup.mul_mem _ hφ hψ))
        rw [Matrix.mulVec_mulVec]
        congr 1
        rw [sub_mul, one_mul, sub_eq_zero] at h0
        exact h0
      rw [h, Submodule.mem_bot, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    · intro w
      rw [h]
      trivial
  have hcomm : ∀ g ∈ H, ∀ g' ∈ H, ∀ v, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ v) =
      (ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    intro g hg g' hg' v
    have h1 := (hF _).1 (hFtop ((ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v))) _
      (Subgroup.commutator_mem_commutator hg hg')
    rw [← h1]
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    congr 3
    rw [commutatorElement_def]
    group
  have hscal : ∀ g ∈ H, ∃ c : k, ∀ v, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := by
    intro g hg
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k))
    refine ⟨c, ?_⟩
    rcases hirr (Module.End.eigenspace (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k)) c) (by
      intro g' hg' v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [hcomm g hg g' hg', hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · intro v
      have : v ∈ Module.End.eigenspace (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k)) c := by
        rw [h]; trivial
      rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
  rcases hirr (Submodule.span k {(![1, 0] : Fin 2 → k)}) (by
    intro g hg v hv
    obtain ⟨c, hc⟩ := hscal g hg
    rw [hc]
    exact Submodule.smul_mem _ _ hv) with h | h
  · rw [Submodule.span_singleton_eq_bot] at h
    have := congrFun h 0
    simp at this
  · have : (![0, 1] : Fin 2 → k) ∈ Submodule.span k {(![1, 0] : Fin 2 → k)} := by
      rw [h]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    have := congrFun hc 1
    simp at this

theorem main (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset GlobalTheory.Ord2.Pl) (A : ValuationSubring Ω) (W : GlobalTheory.Ord2.R2 Ω l) (h : GlobalTheory.Ord2.Nf e S A W) :
    ∃ φ ∈ ⁅GlobalTheory.Ord2.H0g W, GlobalTheory.Ord2.H0g W⁆,
      Matrix.det (GlobalTheory.Ord2.mat W φ - (1 : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l))) ≠ (0 : Formalism.ConjugateSelfDual.Qbar l) := by
  refine exists_comm W (GlobalTheory.Ord2.H0g W) ?_ ?_
  · intro s hs
    have h1 : GlobalTheory.Ord2.dt W s = 1 := hs.2
    have h2 := congrArg Units.val h1
    exact h2
  · intro V hV
    exact h.irr.2.2 V le_top (fun g v hv => hV g g.2 v hv)

end GlobalTheory.CommutingExistence

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  intro l _ Ω _ _ _ e S A W hW c hc s i j

  have hdet : (mat W s).det ∈ c.O := by
    let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W s i j, hc s i j⟩
    have hM : M.map c.O.val = mat W s := by ext i j; rfl
    have h := RingHom.map_det (SubringClass.subtype c.O) M
    rw [RingHom.mapMatrix_apply] at h
    rw [← hM]
    have e1 : (M.map c.O.val) = M.map (SubringClass.subtype c.O) := rfl
    rw [e1, ← h]
    exact (M.det).2

  have hinv : (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
    have h2 : dt W s ^ 2 = 1 := by
      have := congrArg (fun f => f s) hW.det2
      simpa using this
    have : (dt W s)⁻¹ = dt W s := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
    rw [this]; rfl
  have hcyc : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) ∈ c.O := by
    show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O
    exact c.O.algebraMap_mem _
  have hval : mat (dual1 W) s i j = ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) * (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) * mat W s i j := by
    simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, MonoidHom.inv_apply]
  rw [hval, hinv]
  exact c.O.mul_mem (c.O.mul_mem hcyc hdet) (hc s i j)

end GlobalTheory.Ord2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

open Pointwise

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cocycle_mulVec {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (g h : G ℚ Ω) :
    z (g * h) = z g + mat W g *ᵥ z h :=
  hz.2 g h

theorem mat_mul' (W : R2 Ω l) (g h : G ℚ Ω) : mat W (g * h) = mat W g * mat W h := by
  simp [mat, map_mul, Units.val_mul]

theorem mat_one' (W : R2 Ω l) : mat W 1 = 1 := by
  simp [mat]

theorem cob_conj {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (γ t : G ℚ Ω)
    (x : Fin 2 → Qbar l) (ht : z t = mat W t *ᵥ x - x) :
    z (γ * t * γ⁻¹) = mat W (γ * t * γ⁻¹) *ᵥ (mat W γ *ᵥ x - z γ) - (mat W γ *ᵥ x - z γ) := by
  have h0 : z 1 = 0 := by
    have := cocycle_mulVec hz 1 1
    rw [mul_one, mat_one', Matrix.one_mulVec] at this
    simpa using this
  have h2 : z γ⁻¹ = -(mat W γ⁻¹ *ᵥ z γ) := by
    have := cocycle_mulVec hz γ⁻¹ γ
    rw [inv_mul_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hinv : mat W γ⁻¹ * mat W γ = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
  rw [cocycle_mulVec hz, cocycle_mulVec hz, ht, h2, mat_mul', mat_mul', mat_mul']
  simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.mul_one]
  abel

theorem cob_of_conj_le {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (γ : G ℚ Ω)
    (H H' : Subgroup (G ℚ Ω)) (hH : ∀ s ∈ H', γ⁻¹ * s * γ ∈ H)
    (h : ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x) :
    ∃ x : Fin 2 → Qbar l, ∀ s ∈ H', z s = mat W s *ᵥ x - x := by
  obtain ⟨x, hx⟩ := h
  refine ⟨mat W γ *ᵥ x - z γ, fun s hs => ?_⟩
  have e : s = γ * (γ⁻¹ * s * γ) * γ⁻¹ := by group
  rw [e]
  exact cob_conj hz γ _ x (hx _ (hH s hs))

theorem place_indep : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l)
    (z : G ℚ Ω → Fin 2 → Qbar l), z ∈ Z1 (Loc.colRep W) → ∀ (w : Pl) (B B' : ValuationSubring Ω),
    IsPlaceOver B w → IsPlaceOver B' w →
    ((∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, z s = mat W s *ᵥ x - x) →
      ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B', z s = mat W s *ᵥ x - x) ∧ (Triv W B z → Triv W B' z) := by
  intro l _ Ω _ _ _ W z hz w B B' hB hB'
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hB hB'
  refine ⟨cob_of_conj_le hz γ _ _ (fun s hs => ?_), cob_of_conj_le hz γ _ _ (fun s hs => ?_)⟩
  · have := conj_mem_Ine_smul (F := ℚ) (A := B') (γ := γ⁻¹) (σ := s) hs
    rw [inv_inv, ← hγ, inv_smul_smul] at this
    exact this
  · have hs' : s • B' = B' := hs
    show (γ⁻¹ * s * γ) • B = B
    rw [mul_smul, mul_smul, hγ, hs', ← hγ, inv_smul_smul]

end GlobalTheory.Ord2
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_upperTriangular_decompGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  intro l _ Ω _ _ _ e S A W hW s hs
  have h := hW.upper s hs
  simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul] at h ⊢
  rw [h, mul_zero]

end GlobalTheory.Ord2
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings : ∀ D : D7, useNorm D := by
  first | exact @GlobalTheory.ConjNorm.useNorm_all | exact GlobalTheory.ConjNorm.useNorm_all | (intros; apply GlobalTheory.ConjNorm.useNorm_all <;> assumption)
end
