module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006
public import Mathlib.Analysis.Complex.Exponential
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

private theorem exp_real_smul_mem_UJset_of_inG {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) (hX : X.conjTranspose * H + H * X = 0)
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X)).conjTranspose * H * NormedSpace.exp ((t : ℂ) • X) = H := by
  set Y : Matrix (Fin n) (Fin n) ℂ := (t : ℂ) • X with hYdef
  have hHX : H * X = -(X.conjTranspose * H) := eq_neg_of_add_eq_zero_right hX
  have hY : SemiconjBy H Y (-Y.conjTranspose) := by
    show H * Y = -Y.conjTranspose * H
    rw [hYdef, Matrix.mul_smul, hHX, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.neg_mul, Matrix.smul_mul, smul_neg]
  have key : NormedSpace.exp (-(-Y.conjTranspose)) * H * NormedSpace.exp Y = H := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
    letI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
    exact hY.exp_neg_mul_mul_exp_eq_self
  rwa [neg_neg, Matrix.exp_conjTranspose] at key

private theorem mul_mem_UH_Hpk' {k r : ℕ} {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) :
    g * h ∈ B.GV k r := by
  have hg' : g.conjTranspose * Hpk k r * g = Hpk k r := hg
  have hh' : h.conjTranspose * Hpk k r * h = Hpk k r := hh
  show (g * h).conjTranspose * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul, show h.conjTranspose * g.conjTranspose * Hpk k r * (g * h) = h.conjTranspose * (g.conjTranspose * Hpk k r * g) * h by
    simp only [Matrix.mul_assoc], hg', hh']

private theorem exp_smul_mem_UJset' {k r : ℕ} {X : B.Mat k r} (hX : B.inLie k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r :=
  exp_real_smul_mem_UJset_of_inG (Hpk k r) X hX t

private theorem rdV_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : B.Mat k r} (hX : B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, RdV X f g = RdV X f' g := by
  intro g hg
  simp only [RdV]
  congr 1
  funext t
  exact h _ (mul_mem_UH_Hpk' hg (exp_smul_mem_UJset' hX t))

private theorem ldV_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : B.Mat k r} (hX : B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, B.LdV X f g = B.LdV X f' g := by
  intro g hg
  simp only [B.LdV]
  congr 1
  funext t
  have hneg : -((t : ℂ) • X) = ((-t : ℝ) : ℂ) • X := by rw [Complex.ofReal_neg, neg_smul]
  rw [hneg]
  exact h _ (mul_mem_UH_Hpk' (exp_smul_mem_UJset' hX (-t)) hg)

private theorem rw_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : List (B.Mat k r)) (hv : ∀ X ∈ v, B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, B.Rw v f g = B.Rw v f' g := by
  induction v with
  | nil => exact h
  | cons X v ih =>
    exact rdV_congr_on_GV (hv X List.mem_cons_self) (ih fun Y hY => hv Y (List.mem_cons_of_mem X hY))

private theorem dLR_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X)
    {f f' : B.Mat k r → E} (h : ∀ g ∈ B.GV k r, f g = f' g) :
    ∀ g ∈ B.GV k r, B.dLR u v f g = B.dLR u v f' g := by
  induction u with
  | nil => exact rw_congr_on_GV v hv h
  | cons X u ih =>
    exact ldV_congr_on_GV (hu X List.mem_cons_self) (ih fun Y hY => hu Y (List.mem_cons_of_mem X hY))

theorem ckOn_inCC_congr_on_group : ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F F' : B.Mat k r → E), (∀ g ∈ B.GV k r, F g = F' g) → (B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) F') ∧ ∀ m : ℕ, B.InCC A m F → B.InCC A m F' := by
  intro k r E _ _ A F F' h
  have hck : ∀ m : ℕ∞, B.CkOn m (B.GV k r) F → B.CkOn m (B.GV k r) F' := by
    intro m hF g₀ hg₀
    obtain ⟨U, f', hU, hg₀U, hf', hfU⟩ := hF g₀ hg₀
    exact ⟨U, f', hU, hg₀U, hf', fun g hgU hgG => (h g hgG).symm.trans (hfU g hgU hgG)⟩
  refine ⟨hck ⊤, fun m hF => ?_⟩
  unfold B.InCC B.CCle at hF ⊢
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hck _ hc1, fun u v hu hv hlen g hg => ?_⟩
  rw [← dLR_congr_on_GV u v (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1) h g hg]
  exact hc2 u v hu hv hlen g hg

end GlobalTheory
end

section

open Formalism.REAL Finset

namespace GlobalTheory

theorem prod_add_ite_shift {n : ℕ} (ν : Fin n → ℂ) (s : Fin n) (u : ℂ) :
    (∏ t, (u + ν t + if t = s then 1 else 0)) =
      (∏ t, (u + ν t)) + ∏ t ∈ Finset.univ.erase s, (u + ν t) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s),
    ← Finset.mul_prod_erase Finset.univ (fun t => u + ν t) (Finset.mem_univ s)]
  have : ∏ t ∈ Finset.univ.erase s, (u + ν t + if t = s then 1 else 0) =
      ∏ t ∈ Finset.univ.erase s, (u + ν t) :=
    Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]
  rw [this]; simp only [if_true]; ring

theorem qdet_vector_multiplier_shift_plus : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), GlRel E → GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t + if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  cases n with
  | zero => exact j.elim0
  | succ m =>
  let M : (Fin (m + 1) → Fin (m + 1) → Module.End ℂ W) → Module.End ℂ (Fin (m + 1) → W) :=
    fun B => LinearMap.pi fun a => ∑ k, (B a k).comp (LinearMap.proj k)
  have hM : ∀ B y a, M B y a = ∑ k, B a k (y k) := by
    intro B y a
    simp [M, LinearMap.sum_apply]
  let Ω := M (fun l a => E' a l)
  let X : ℂ → Module.End ℂ (Fin (m + 1) → W) := fun u => M (fun a k =>
    ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1))
  choose c hc using fun a k : Fin (m + 1) =>
    GlobalTheory.T.exists_qminor_sub_eq_polynomial (Module.End ℂ W) (m + 1) m E' (Fin.succAbove a) (Fin.succAbove k) 1
  have hXc : ∀ u, X u = ∑ i ∈ Finset.range (m + 1), u ^ i •
      M (fun a k => ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • c a k i) := by
    intro u
    refine LinearMap.ext fun y => funext fun a => ?_
    simp only [X, hM, hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
      Pi.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  have hΩ : ∀ (u : ℂ) (y : Fin (m + 1) → W),
      u • X u y + Ω (X u y) = (∏ s, (u + ν s)) • y := by
    intro u y
    funext l
    have h1 : (u • X u y + Ω (X u y)) l = ∑ a, Tm E' u a l (X u y a) := by
      simp only [Pi.add_apply, Pi.smul_apply, Ω, hM, Tm, LinearMap.add_apply,
        Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single l]
      · simp [Finset.smul_sum]
      · intro b _ hb; simp [hb]
      · simp
    have h2 : ∀ k : Fin (m + 1), ∑ a : Fin (m + 1), Tm E' u a l ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k)) = if l = k then qdet E' u (y k) else 0 := by
      intro k
      have := LinearMap.congr_fun (GlobalTheory.T.capelli_left_comatrix_qminor_eq (Module.End ℂ W) m E' hE' u k l) (y k)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
      simp only [LinearMap.smul_apply, map_smul]
      rw [this]
      split_ifs <;> simp
    rw [h1]

    simp only [X, hM, map_sum]
    rw [Finset.sum_comm]
    simp only [h2]
    simp [hq]
  obtain ⟨v, hv, hXv⟩ := GlobalTheory.T.exists_eigenSplit_of_resolventIdentity (Fin (m + 1) → W) (m + 1) Ω X (m + 1) _ ν hν hXc hΩ
    (Pi.single j w)
  have hqι : ∀ u y, qdet E u (ι y) = (∏ s, (u + ν s)) • ι y := by
    intro u y
    rw [← map_smul, ← hq]
    exact (GlobalTheory.T.qminor_intertwining_apply V W (m + 1) (m + 1) E E' ι hι id id u y).symm
  have hmu : ∀ (u : ℂ) (y : Fin (m + 1) → W), qdet E u (∑ a, x a (ι (y a))) =
      (∏ s, (u + ν s)) • (∑ a, x a (ι (y a))) + ∑ a, x a (ι (X u y a)) := by
    intro u y
    have h3 : ∀ k : Fin (m + 1), qdet E u (x k (ι (y k))) = (∏ s, (u + ν s)) • x k (ι (y k)) +
        ∑ a : Fin (m + 1), x a (ι ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k))) := by
      intro k
      have := LinearMap.congr_fun (GlobalTheory.T.capelliDet_mul_vectorType (Module.End ℂ V) m E x hE hx u k) (ι (y k))
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
        LinearMap.add_apply, hqι, map_smul] at this
      rw [this]
      simp only [LinearMap.smul_apply, map_smul, GlobalTheory.T.qminor_intertwining_apply V W (m + 1) m E E' ι hι]

    simp only [map_sum, h3, Finset.sum_add_distrib, Finset.smul_sum, X, hM]
    rw [Finset.sum_comm]
  refine ⟨v, ?_, fun s u => ?_⟩
  · rw [Finset.sum_comm]
    have : ∀ a, ∑ s, x a (ι (v s a)) = x a (ι ((Pi.single j w : Fin (m + 1) → W) a)) := by
      intro a
      rw [hv]

      simp [map_sum]
    simp only [this]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  · rw [hmu, hXv, prod_add_ite_shift, add_smul]
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum]

end GlobalTheory
end

section

namespace GlobalTheory

open scoped NNReal

noncomputable def expNegTop : WithTop ℚ → ℝ≥0
  | ⊤ => 0
  | (q : ℚ) => ⟨Real.exp (-(q : ℝ)), (Real.exp_pos _).le⟩

@[simp] theorem expNegTop_top : expNegTop ⊤ = 0 := rfl

theorem expNegTop_coe (q : ℚ) : ((expNegTop (q : WithTop ℚ) : ℝ≥0) : ℝ) = Real.exp (-(q : ℝ)) := rfl

theorem expNegTop_zero : expNegTop 0 = 1 := by
  apply NNReal.coe_injective
  have h := expNegTop_coe 0
  simpa using h

theorem expNegTop_add (a b : WithTop ℚ) : expNegTop (a + b) = expNegTop a * expNegTop b := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      apply NNReal.coe_injective
      rw [← WithTop.coe_add, NNReal.coe_mul, expNegTop_coe, expNegTop_coe, expNegTop_coe,
        ← Real.exp_add]
      push_cast
      ring_nf

theorem expNegTop_le_iff (a b : WithTop ℚ) : expNegTop a ≤ expNegTop b ↔ b ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top =>
      rw [← NNReal.coe_le_coe, expNegTop_coe]
      simp only [expNegTop_top, NNReal.coe_zero, top_le_iff, WithTop.coe_ne_top, iff_false, not_le]
      exact Real.exp_pos _
    | coe b =>
      rw [← NNReal.coe_le_coe, expNegTop_coe, expNegTop_coe, Real.exp_le_exp, neg_le_neg_iff,
        Rat.cast_le, WithTop.coe_le_coe]

noncomputable def expNegValuation {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    Valuation F ℝ≥0 where
  toFun x := expNegTop (v x)
  map_zero' := by simp
  map_one' := by simp [expNegTop_zero]
  map_mul' x y := by rw [v.map_mul, expNegTop_add]
  map_add_le_max' x y := by
    rcases min_le_iff.mp (v.map_add x y) with h | h
    · exact le_max_of_le_left ((expNegTop_le_iff _ _).mpr h)
    · exact le_max_of_le_right ((expNegTop_le_iff _ _).mpr h)

theorem expNegValuation_apply {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x = expNegTop (v x) := rfl

theorem expNegValuation_le_one_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x ≤ 1 ↔ 0 ≤ v x := by
  rw [expNegValuation_apply, ← expNegTop_zero, expNegTop_le_iff]

theorem exists_nnreal_valuation_of_addValuation :
    ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)), ∃ v' : Valuation F NNReal,
      (∀ x y, v' x ≤ v' y ↔ v y ≤ v x) ∧ v'.Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  intro F _ v
  refine ⟨expNegValuation v, fun x y => expNegTop_le_iff _ _, ?_, ?_, ?_⟩
  · exact Subtype.val_injective
  · intro x
    exact (expNegValuation_le_one_iff v _).mpr x.2
  · intro r hr
    exact ⟨⟨r, (expNegValuation_le_one_iff v r).mp hr⟩, rfl⟩

end GlobalTheory
end

section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

theorem exists_extend_character {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  first
  | exact @_root_.GlobalTheory.DivisibleUnits.target
  | exact _root_.GlobalTheory.DivisibleUnits.target
  | (apply _root_.GlobalTheory.DivisibleUnits.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.DivisibleUnits.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DivisibleUnits.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DivisibleUnits.target ..)

variable {O : Type} [CommRing O]

theorem exists_ptMap {A R : Type} [CommRing A] [Algebra O A] [CommRing R] [Algebra O R]
    (c : specO O R ⟶ specO O A) : ∃ φ : A →ₐ[O] R, c = ptMap φ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of R) c.left
  have w := Over.w c
  change c.left ≫ Spec.map _ = Spec.map _ at w
  rw [← hψ, ← Spec.map_comp] at w
  have w' := congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  exact ⟨⟨ψ.hom, fun r => RingHom.congr_fun w' r⟩, Over.OverMorphism.ext hψ.symm⟩

theorem exists_finite_free [IsLocalRing O] (Z : Over (Spec (CommRingCat.of O))) [IsFinite Z.hom] [Flat Z.hom] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A), Module.Finite O A ∧ Module.Free O A ∧
      Nonempty (specO O A ≅ Z) := by
  haveI : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let g : CommRingCat.of O ⟶ Γ(Z.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ Z.hom.appTop
  letI : Algebra O Γ(Z.left, ⊤) := g.hom.toAlgebra
  have hw : Z.left.isoSpec.inv ≫ Z.hom = Spec.map g := by
    rw [Iso.inv_comp_eq, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]
  haveI h1 : IsFinite (Spec.map g) := hw ▸ inferInstance
  haveI h2 : Flat (Spec.map g) := hw ▸ inferInstance
  have h3 : g.hom.Finite := (IsFinite.SpecMap_iff g).1 h1
  have h4 : g.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h2
  haveI : Module.Finite O Γ(Z.left, ⊤) := h3
  haveI : Module.Flat O Γ(Z.left, ⊤) := h4
  exact ⟨Γ(Z.left, ⊤), inferInstance, inferInstance, inferInstance, Module.free_of_flat_of_isLocalRing,
    ⟨Over.isoMk Z.left.isoSpec.symm hw⟩⟩

theorem exists_algHom_valuationSubring {F : Type} [Field F] (W : ValuationSubring F) {A : Type} [CommRing A]
    [Algebra W A] [Module.Finite W A] (φ : A →ₐ[W] F) : ∃ ψ : A →ₐ[W] W, φ = (Algebra.ofId W F).comp ψ := by
  have h : ∀ a, φ a ∈ (⊥ : Subalgebra W F) := fun a => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := W) a).map φ)
    exact Algebra.mem_bot.2 ⟨y, hy⟩
  let e := Algebra.botEquivOfInjective (R := W) (A := F) Subtype.val_injective
  refine ⟨(e : (⊥ : Subalgebra W F) →ₐ[W] W).comp (φ.codRestrict ⊥ h), AlgHom.ext fun a => ?_⟩
  obtain ⟨y, hy⟩ := e.symm.surjective (φ.codRestrict ⊥ h a)
  show φ a = algebraMap W F (e (φ.codRestrict ⊥ h a))
  rw [← hy, e.apply_symm_apply]
  exact (congrArg Subtype.val hy).symm.trans ((e.symm.commutes y ▸ rfl : ((e.symm y : (⊥ : Subalgebra W F)) : F) = _))

theorem isAdicComplete_of_pow_le {I J : Ideal O} [IsAdicComplete I O] {a b : ℕ} (h₁ : I ^ a ≤ J) (h₂ : J ^ b ≤ I) :
    IsAdicComplete J O := by
  letI : TopologicalSpace O := I.adicTopology
  haveI : IsTopologicalRing O := (I.ringFilterBasis).isTopologicalRing
  letI : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  haveI : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  have hI : IsAdic I := rfl
  have hJ : IsAdic J := by
    rw [isAdic_iff] at hI ⊢
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · refine AddSubgroup.isOpen_mono (H₁ := (I ^ (a * n)).toAddSubgroup) (H₂ := (J ^ n).toAddSubgroup) ?_ (hI.1 _)
      intro x hx
      rw [pow_mul] at hx
      exact Ideal.pow_right_mono h₁ n hx
    · obtain ⟨n, hn⟩ := hI.2 s hs
      refine ⟨b * n, fun x hx => hn ?_⟩
      rw [pow_mul] at hx
      exact Ideal.pow_right_mono h₂ n hx
  exact hJ.isAdicComplete_iff.2 (hI.isAdicComplete_iff.1 inferInstance)

section Val
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem exists_pow_mem_span (a b : TWO.Ov v) (ha : ¬ IsUnit a) (hb : b ≠ 0) :
    ∃ n : ℕ, a ^ n ∈ Ideal.span {b} := by
  by_cases ha0 : a = 0
  · exact ⟨1, by simp [ha0]⟩
  have hbF : (b : F) ≠ 0 := fun h => hb (Subtype.ext h)
  have haF : (a : F) ≠ 0 := fun h => ha0 (Subtype.ext h)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff v).2 haF)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff v).2 hbF)
  have hr0 : 0 < r := by
    have h0 : (0 : ℚ) ≤ r := by have := TWO.v_nonneg v a; rw [← hr] at this; exact_mod_cast this
    refine lt_of_le_of_ne h0 fun h => ha ?_
    have hi : (a : F)⁻¹ ∈ TWO.Ov v := by
      refine TWO.exists_weight_basis_filtration (a := v a) ?_ (by rw [← hr, ← h]; rfl)
      rw [← AddValuation.map_mul, mul_inv_cancel₀ haF, AddValuation.map_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ haF))
  obtain ⟨n, hn⟩ := Archimedean.arch s hr0
  have hq : (a : F) ^ n / b ∈ TWO.Ov v := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
      ((AddValuation.ne_top_iff v).2 (div_ne_zero (pow_ne_zero n haF) hbF))
    have e : v ((a : F) ^ n / b * b) = v ((a : F) ^ n) := by rw [div_mul_cancel₀ _ hbF]
    rw [AddValuation.map_mul, AddValuation.map_pow, ← ht, ← hs, ← hr] at e
    have e' : t + s = n • r := by exact_mod_cast e
    rw [TWO.mem_Ov, ← ht]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t)
  exact ⟨n, Ideal.mem_span_singleton'.2 ⟨⟨_, hq⟩, Subtype.ext (by
    show (a : F) ^ n / b * b = ((a ^ n : TWO.Ov v) : F)
    rw [div_mul_cancel₀ _ hbF]; rfl)⟩⟩

end Val

end GlobalTheory.TorsionCharacter
end
end
