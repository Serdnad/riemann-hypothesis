module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoCoeffZero
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import ReciprocityTheory.GaloisValuations.Bundle002

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PerpFrameTranslate

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

variable {P Q P' Q' : ℕ}

theorem act_mul (g h : UpqT P Q) (x : Sp P Q) : act (g * h) x = act g (act h x) := by
  unfold act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : Sp P Q) : act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem act_inv_act (g : UpqT P Q) (x : Sp P Q) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : UpqT P Q) (x : Sp P Q) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem herm_eq_dot (x y : Sp P Q) : herm x y = star y ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ x) := by
  rw [herm_eq_hform]
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]
  rfl

theorem herm_act (g : UpqT P Q) (x y : Sp P Q) : herm (act g x) (act g y) = herm x y := by
  have hu : (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2
  rw [herm_eq_dot, herm_eq_dot, act, act, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]

theorem herm_eq_sum (x y : Sp P Q) : herm x y = ∑ i, (sg i : ℂ) * (x i * star (y i)) := by
  simp [herm, sg, Fintype.sum_sum_type, sub_eq_add_neg]

def incl (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ :=
  Matrix.of fun i b => if i = e (some b) then 1 else 0

theorem incl_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (u : Sp P' Q') :
    (incl e *ᵥ u) (e none) = 0 := by
  simp [incl, Matrix.mulVec, dotProduct]

theorem incl_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (u : Sp P' Q')
    (b : Fin P' ⊕ Fin Q') : (incl e *ᵥ u) (e (some b)) = u b := by
  simp [incl, Matrix.mulVec, dotProduct]

theorem ext_coord (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) {x y : Sp P Q}
    (h0 : x (e none) = y (e none)) (h1 : ∀ b, x (e (some b)) = y (e (some b))) : x = y := by
  funext i
  obtain ⟨i, rfl⟩ := e.surjective i
  rcases i with _ | b
  · exact h0
  · exact h1 b

theorem isPerpEmb_base (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e)
    (j₀ : UpqT P' Q' → UpqT P Q) (hj : IsBlockEmb e j₀) :
    IsPerpEmb (baseVec e) (incl e) j₀ := by
  refine ⟨fun u v => ?_, fun y => ?_, fun g => ⟨?_, fun u => ?_⟩⟩
  · rw [herm_eq_sum, herm_eq_sum, ← e.sum_comp, Fintype.sum_option]
    simp only [incl_none, incl_some, he _, zero_mul, mul_zero, zero_add]
  · have h1 : herm y (baseVec e) = (sg (e none) : ℂ) * y (e none) := by
      rw [herm_eq_sum, ← e.sum_comp, Fintype.sum_option]
      simp [baseVec]
    have h2 : (sg (e none) : ℂ) ≠ 0 := by exact_mod_cast sg_ne_zero _
    rw [h1, mul_eq_zero, or_iff_right h2]
    constructor
    · intro h
      exact ⟨fun b => y (e (some b)), ext_coord e (by rw [incl_none, h]) fun b => incl_some e _ b⟩
    · rintro ⟨u, rfl⟩
      exact incl_none e u
  · obtain ⟨h1, -, h3, -⟩ := hj g
    refine ext_coord e ?_ fun b => ?_
    · simp [act, baseVec, h1]
    · simp [act, baseVec, h3]
  · obtain ⟨-, h2, -, h4⟩ := hj g
    have key : ∀ i, act (j₀ g) (incl e *ᵥ u) i =
        ∑ b, UpqT.mat (j₀ g) i (e (some b)) * u b := fun i => by
      change ∑ k, UpqT.mat (j₀ g) i k * (incl e *ᵥ u) k = _
      rw [← e.sum_comp, Fintype.sum_option]
      simp only [incl_none, incl_some, mul_zero, zero_add]
    refine ext_coord e ?_ fun b => ?_
    · rw [key, incl_none]; simp [h2]
    · rw [key, incl_some]; simp only [h4]; rfl

theorem isPerpEmb_translate {x₀ : Sp P Q} {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    {j : UpqT P' Q' → UpqT P Q} (h : IsPerpEmb x₀ A j) (g₀ : UpqT P Q) :
    IsPerpEmb (act g₀ x₀) (UpqT.mat g₀ * A) (fun g => g₀ * j g * g₀⁻¹) := by
  have hA : ∀ u, (UpqT.mat g₀ * A) *ᵥ u = act g₀ (A *ᵥ u) := fun u => by
    rw [act, Matrix.mulVec_mulVec]
  refine ⟨fun u v => ?_, fun y => ?_, fun g => ⟨?_, fun u => ?_⟩⟩
  · rw [hA, hA, herm_act, h.1]
  · rw [← act_act_inv g₀ y, herm_act, h.2.1]
    refine exists_congr fun u => ?_
    rw [hA]
    constructor
    · intro hu; rw [hu]
    · intro hu; rw [← act_inv_act g₀ (A *ᵥ u), hu, act_inv_act]
  · simp only [act_mul, act_inv_act, (h.2.2 g).1]
  · simp only [hA, act_mul, act_inv_act, (h.2.2 g).2]

theorem exists_isPerpEmb : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ j₀ : UpqT P' Q' → UpqT P Q, IsBlockEmb e j₀ → ∀ g₀ : UpqT P Q,
    ∃ A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ,
      IsPerpEmb (act g₀ (baseVec e)) A (fun g => g₀ * j₀ g * g₀⁻¹) :=
  fun _ _ _ _ e he j₀ hj g₀ => ⟨_, isPerpEmb_translate (isPerpEmb_base e he j₀ hj) g₀⟩

end GlobalTheory.PerpFrameTranslate
end
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.ExpBallCompare

variable {P Q : ℕ}

theorem entry_le_l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (i j) : ‖Z i j‖ ≤ l1 Z :=
  (Finset.single_le_sum (f := fun j => ‖Z i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))

theorem l1_add_le (Z W : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    l1 (Z + W) ≤ l1 Z + l1 W := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem l1_neg (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : l1 (-Z) = l1 Z := by
  simp [l1]

theorem exists_l1_ball {S : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} (hS : S ∈ 𝓝 0) :
    ∃ δ > 0, ∀ Z, l1 Z < δ → Z ∈ S := by
  have hS' : S ∈ 𝓝 (0 : (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) := hS
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hS'
  refine ⟨δ, hδ, fun Z hZ => h ?_⟩
  exact mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 fun i => (pi_norm_lt_iff hδ).2 fun j =>
    (entry_le_l1 Z i j).trans_lt hZ)

theorem exp_isLittleO (A : Type) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    (fun Z : A => NormedSpace.exp Z - 1 - Z) =o[𝓝 0] fun Z => Z := by
  have h := (hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := A)).isLittleO
  simpa using h

theorem eventually_l1_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ in 𝓝 0,
      l1 (NormedSpace.exp Z - 1 - Z) ≤ ε * l1 Z := by
  let : NormedRing (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := FiniteDimensional.complete ℂ _
  have hrow : ∀ (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i, ∑ j, ‖Z i j‖ ≤ ‖Z‖ := by
    intro Z i
    rw [Matrix.linfty_opNorm_def]
    have := Finset.le_sup (f := fun i => ∑ j, ‖Z i j‖₊) (Finset.mem_univ i)
    have h2 := NNReal.coe_le_coe.2 this
    simpa using h2
  have h1 : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, l1 Z ≤ (P + Q : ℝ) * ‖Z‖ := by
    intro Z
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => ∑ j, ‖Z i j‖) ‖Z‖ fun i _ => hrow Z i
    simpa [l1] using this
  have h2 : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, ‖Z‖ ≤ l1 Z := by
    intro Z
    rw [Matrix.linfty_opNorm_def]
    have : (Finset.univ.sup fun i => ∑ j, ‖Z i j‖₊) ≤ ∑ i, ∑ j, ‖Z i j‖₊ :=
      Finset.sup_le fun i _ => Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h2 := NNReal.coe_le_coe.2 this
    simpa [l1] using h2
  have hN : (0 : ℝ) < P + Q + 1 := by positivity
  have h3 := (exp_isLittleO (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).def (div_pos hε hN)
  filter_upwards [h3] with Z hZ
  calc l1 (NormedSpace.exp Z - 1 - Z) ≤ (P + Q : ℝ) * ‖NormedSpace.exp Z - 1 - Z‖ := h1 _
    _ ≤ (P + Q + 1 : ℝ) * (ε / (P + Q + 1) * ‖Z‖) :=
      mul_le_mul (by linarith) hZ (norm_nonneg _) hN.le
    _ = ε * ‖Z‖ := by field_simp
    _ ≤ ε * l1 Z := mul_le_mul_of_nonneg_left (h2 Z) hε.le

theorem exists_l1_exp {t : ℝ} (ht : 1 < t) : ∃ δ > 0,
    ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, l1 Z < δ →
      l1 (NormedSpace.exp Z - 1) ≤ t * l1 Z ∧ l1 Z ≤ t * l1 (NormedSpace.exp Z - 1) := by
  have ht0 : 0 < t := by linarith
  have hε : 0 < 1 - t⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ ht)
  obtain ⟨δ, hδ, h⟩ := exists_l1_ball
    ((eventually_l1_exp (P := P) (Q := Q) hε).and (eventually_l1_exp (sub_pos.2 ht)))
  refine ⟨δ, hδ, fun Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := h Z hZ
  constructor
  · have := l1_add_le (NormedSpace.exp Z - 1 - Z) Z
    rw [sub_add_cancel] at this
    linarith
  · have := l1_add_le (NormedSpace.exp Z - 1) (-(NormedSpace.exp Z - 1 - Z))
    rw [l1_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    have h3 : t⁻¹ * l1 Z ≤ l1 (NormedSpace.exp Z - 1) := by linarith
    exact (inv_mul_le_iff₀ ht0).1 h3

theorem exists_gauge_ball {S : Set (UpqT P Q)} (hS : S ∈ 𝓝 (1 : UpqT P Q)) :
    ∃ δ > 0, ∀ g, gauge g < δ → g ∈ S := by
  rw [GlobalTheory.UpqTopology.isClosedEmbedding_mat.isInducing.nhds_eq_comap] at hS
  obtain ⟨T, hT, hTS⟩ := hS
  have h1 : UpqT.mat (1 : UpqT P Q) = 1 := rfl
  have c : Continuous fun Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Z + 1 :=
    continuous_id.add continuous_const
  obtain ⟨δ, hδ, h⟩ := exists_l1_ball (c.continuousAt.preimage_mem_nhds (x := 0) (t := T)
    (by rw [zero_add, ← h1]; exact hT))
  refine ⟨δ, hδ, fun g hg => hTS ?_⟩
  simpa using h _ hg

theorem expBall_compare : ∀ (P Q : ℕ) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), expBall P Q (t⁻¹ * r) ⊆ {g : UpqT P Q | gauge g < r} ∧ {g : UpqT P Q | gauge g < r} ⊆ expBall P Q (t * r) := by
  intro P Q t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨δ, hδ, h⟩ := exists_l1_exp (P := P) (Q := Q) ht
  obtain ⟨η, hη, h'⟩ := exists_gauge_ball (GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds P Q δ hδ)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hη)] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hrδ : r < δ := hr1.trans_le (min_le_left _ _)
  have hrη : r < η := hr1.trans_le (min_le_right _ _)
  constructor
  · rintro g ⟨X, hX, hg⟩
    have hX' : l1 (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) < t⁻¹ * r := hX
    have h1 : t⁻¹ * r ≤ r := mul_le_of_le_one_left hr0.le (inv_lt_one_of_one_lt₀ ht).le
    have h2 := (h X (by linarith)).1
    have h3 := (lt_inv_mul_iff₀ ht0).1 hX'
    show l1 (UpqT.mat g - 1) < r
    rw [hg]
    linarith
  · intro g hg
    have hg' : l1 (UpqT.mat g - 1) < r := hg
    obtain ⟨X, hX, hgX⟩ := h' g (lt_trans hg hrη)
    refine ⟨X, ?_, hgX⟩
    have h2 := (h X hX).2
    rw [hgX] at hg'
    exact h2.trans_lt (mul_lt_mul_of_pos_left hg' ht0)

end GlobalTheory.ExpBallCompare
end

section

noncomputable section

namespace GlobalTheory.CompactDualQuot.PerpConj

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

variable {P Q P' Q' : ℕ}

theorem jpq_apply (a b : Fin P ⊕ Fin Q) :
    Formalism.UG.Jpq P Q a b = if a = b then (sg a : ℂ) else 0 := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, sg, Matrix.one_apply]
  all_goals (split_ifs <;> simp)

theorem herm_eq_sum (x y : Sp P Q) : herm x y = ∑ i, (sg i : ℂ) * (x i * star (y i)) := by
  simp [herm, sg, Fintype.sum_sum_type, sub_eq_add_neg]

theorem herm_swap (x y : Sp P Q) : herm y x = star (herm x y) := by
  simp [herm_eq_sum, mul_comm]

theorem gram_apply (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (i l : Fin P ⊕ Fin Q) :
    (uᴴ * Formalism.UG.Jpq P Q * u) i l = herm (fun a => u a l) (fun a => u a i) := by
  simp only [Matrix.mul_apply, jpq_apply, herm_eq_sum, conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem herm_single (a b : Fin P ⊕ Fin Q) :
    herm (Pi.single b 1 : Sp P Q) (Pi.single a 1) = if a = b then (sg a : ℂ) else 0 := by
  rw [herm_eq_sum, Finset.sum_eq_single a]
  · by_cases h : a = b <;> simp [h]
  · intro c _ hc; simp [hc]
  · simp

theorem perp_conj : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ j₀ : UpqT P' Q' → UpqT P Q, IsBlockEmb e j₀ →
    ∀ (x₀ : Sp P Q) (A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ) (j : UpqT P' Q' → UpqT P Q),
    qf x₀ = sg (e none) → IsPerpEmb x₀ A j →
    ∃ g₀ : UpqT P Q, act g₀ (baseVec e) = x₀ ∧ ∀ g, j g = g₀ * j₀ g * g₀⁻¹ := by
  intro P Q P' Q' e he j₀ hj₀ x₀ A j hx ⟨h1, h2, h3⟩
  let u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    Matrix.of fun a l => (e.symm l).elim (x₀ a) (fun b => A a b)
  have un : ∀ a, u a (e none) = x₀ a := fun a => by simp [u]
  have us : ∀ a b, u a (e (some b)) = A a b := fun a b => by simp [u]
  have cn : (fun a => u a (e none)) = x₀ := funext un
  have cs : ∀ b, (fun a => u a (e (some b))) = A *ᵥ Pi.single b 1 := fun b => by
    funext a; simp [us]
  have hu : u ∈ Set.range (UpqT.mat (P := P) (Q := Q)) := by
    rw [GlobalTheory.UpqTopology.range_mat]
    ext i l
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨l, rfl⟩ := e.surjective l
    rw [gram_apply, jpq_apply]
    rcases i with _ | i <;> rcases l with _ | l
    · rw [cn, herm_self, hx, if_pos rfl]
    · rw [cn, cs, (h2 _).2 ⟨_, rfl⟩, if_neg (by simp)]
    · rw [cn, cs, herm_swap, (h2 _).2 ⟨_, rfl⟩, if_neg (by simp), star_zero]
    · rw [cs, cs, h1, herm_single, he i]
      simp
  obtain ⟨g₀, hg₀⟩ := hu
  refine ⟨g₀, ?_, fun g => ?_⟩
  · funext a
    simp [act, baseVec, hg₀, un]
  · rw [eq_mul_inv_iff_mul_eq]
    apply GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
    change UpqT.mat (j g) * UpqT.mat g₀ = UpqT.mat g₀ * UpqT.mat (j₀ g)
    rw [hg₀]
    obtain ⟨b1, b2, b3, b4⟩ := hj₀ g
    ext a l
    obtain ⟨l, rfl⟩ := e.surjective l
    rw [Matrix.mul_apply (M := u), ← e.sum_comp, Fintype.sum_option]
    rcases l with _ | l
    · have := congrFun (h3 g).1 a
      simp only [b1, b3, un, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
      rw [← this]
      simp [act, Matrix.mul_apply, Matrix.mulVec, dotProduct, un]
    · have := congrFun ((h3 g).2 (Pi.single l 1)) a
      simp only [b2, b4, us, mul_zero, zero_add]
      simp only [act, Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, us] using this

end GlobalTheory.CompactDualQuot.PerpConj
end
end

section

open IsLocalRing Matrix

namespace GlobalTheory.DualNumberLocal

theorem main : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], ∃ _ : IsLocalRing (DualNumber O), IsNoetherianRing (DualNumber O) ∧ IsAdicComplete (maximalIdeal (DualNumber O)) (DualNumber O) ∧ IsLocalHom (algebraMap O (DualNumber O)) ∧ Function.Surjective (fun x : O => residue (DualNumber O) (algebraMap O (DualNumber O) x)) ∧ ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by
  intro O _ _ _ _
  haveI hloc : IsLocalRing (DualNumber O) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
      exact isUnit_or_isUnit_one_sub_self _
  haveI : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have hmem : ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by
    intro z
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  refine ⟨hloc, IsNoetherianRing.of_finite O (DualNumber O),
    GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O), ?_, ?_, hmem⟩
  · refine ⟨fun a h => ?_⟩
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.isUnit_iff_isUnit_fst,
      TrivSqZeroExt.fst_inl] at h
    exact h
  · intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨z.fst, ?_⟩
    show residue (DualNumber O) (algebraMap O (DualNumber O) z.fst) = residue (DualNumber O) z
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmem,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self]
    exact Ideal.zero_mem _

end GlobalTheory.DualNumberLocal
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMRam

open WeierstrassCurve

theorem exists_conj_lattice (σ : ℂ ≃+* ℂ) (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ := by
  first
  | exact @_root_.GlobalTheory.DiscUniformisation.main
  | exact _root_.GlobalTheory.DiscUniformisation.main
  | (apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiscUniformisation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiscUniformisation.main ..)

end GlobalTheory.CMRam
end
end

section

open NumberField IsDedekindDomain Pointwise

namespace GlobalTheory.PlaceConjQ

theorem eq_of_prime_mem {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have : Fact q.Prime := ⟨hq⟩
  have := v.isPrime
  have := w.isPrime
  have h1 := ((ReciprocityTheory.Gal.liesOver_span_iff q v.asIdeal).2 hv).over
  have h2 := ((ReciprocityTheory.Gal.liesOver_span_iff q w.asIdeal).2 hw).over
  apply HeightOneSpectrum.ext
  ext x
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  have e : Rat.ringOfIntegersEquiv.symm n = algebraMap ℤ (𝓞 ℚ) n :=
    (eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n).trans (eq_intCast (algebraMap ℤ (𝓞 ℚ)) n).symm
  rw [e, ← Ideal.mem_comap, ← Ideal.mem_comap]
  change n ∈ v.asIdeal.under ℤ ↔ n ∈ w.asIdeal.under ℤ
  rw [← h1, ← h2]

end GlobalTheory.PlaceConjQ
end
