module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.FlagUnipotentLattices.StabiliserComplementDecomposition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.PeriodIntegrals.Bundle020
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset Filter Topology
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory.DerivedBracket

open PI.UpqRep PI.UnitaryGroupMassFormula.CapelliEig GlobalTheory.DerivedAction

theorem fderiv_comm {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {x : E} (hF : ContDiffAt ℝ ∞ F x) (L M : E →L[ℝ] E) {a b c : E}
    (ha : M x = a) (hb : L x = b) (hc : L a - M b = c) :
    fderiv ℝ (fun g => fderiv ℝ F g (L g)) x a - fderiv ℝ (fun g => fderiv ℝ F g (M g)) x b =
      fderiv ℝ F x c := by
  subst ha hb hc
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by simp)
  have hs : IsSymmSndFDerivAt ℝ F x :=
    hF.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  rw [(hD.hasFDerivAt.clm_apply L.hasFDerivAt).fderiv, (hD.hasFDerivAt.clm_apply M.hasFDerivAt).fderiv]
  simp [hs (M x) (L x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}

theorem lie_bracket {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) :
    InLieHpk k r (X * Y - Y * X) := by
  have hLX : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  have hLY : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
  show (X * Y - Y * X)ᴴ * Hpk k r + Hpk k r * (X * Y - Y * X) = 0
  have e1 : Yᴴ * Xᴴ * Hpk k r = Hpk k r * (Y * X) := by
    rw [Matrix.mul_assoc, hLX, Matrix.mul_neg, ← Matrix.mul_assoc, hLY, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e2 : Xᴴ * Yᴴ * Hpk k r = Hpk k r * (X * Y) := by
    rw [Matrix.mul_assoc, hLY, Matrix.mul_neg, ← Matrix.mul_assoc, hLX, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

theorem dsig_dsig (hσ : IsDSHpk k r ε mu σ) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) {F : Mx k r → H} {U : Set (Mx k r)}
    (hU : IsOpen U) (h1 : (1 : Mx k r) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUH (Hpk k r) h → σ h v = F h) (L : Mx k r →L[ℝ] Mx k r) (hL : ∀ x, L x = x * Y) :
    dsig (k := k) (r := r) σ X (dsig (k := k) (r := r) σ Y v) =
      fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X := by
  have hG : ContDiffOn ℝ ∞ (fun g => fderiv ℝ F g (L g)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  have hGe : ∀ g ∈ U, inUH (Hpk k r) g → σ g (dsig (k := k) (r := r) σ Y v) = fderiv ℝ F g (L g) := by
    intro g hg hgH
    have h1 := hasDerivAt_local hY hU hg hF hfF hgH
    have h2 := hasDerivAt_apply hY hv (σ g)
    have e : (fun u : ℝ => σ (g * NormedSpace.exp ((u : ℂ) • Y)) v) =
        fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • Y)) v) := by
      funext t
      rw [Hecke_multiplication k r ε mu H σ hσ g hgH _ (exp_mem hY t)]
      rfl
    rw [e] at h1
    simp only [hL]
    exact h2.unique h1
  have h := hasDerivAt_local (f := fun g => σ g (dsig (k := k) (r := r) σ Y v)) hX hU h1 hG hGe one_mem
  simp only [Matrix.one_mul] at h
  exact h.deriv

theorem dsig_bracket (hσ : IsDSHpk k r ε mu σ) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (dsig (k := k) (r := r) σ Y v) -
      dsig (k := k) (r := r) σ Y (dsig (k := k) (r := r) σ X v) = dsig (k := k) (r := r) σ (X * Y - Y * X) v := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 one_mem
  have h := hasDerivAt_local (lie_bracket hX hY) hU h1 hF hfF one_mem
  simp only [Matrix.one_mul] at h
  have e : dsig (k := k) (r := r) σ (X * Y - Y * X) v = fderiv ℝ F 1 (X * Y - Y * X) := h.deriv
  let L : Mx k r →L[ℝ] Mx k r := (LinearMap.mulRight ℝ Y).toContinuousLinearMap
  have hL : ∀ x, L x = x * Y := by intro x; simp [L]
  let M : Mx k r →L[ℝ] Mx k r := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hM : ∀ x, M x = x * X := by intro x; simp [M]
  rw [dsig_dsig hσ hX hY hv hU h1 hF hfF L hL, dsig_dsig hσ hY hX hv hU h1 hF hfF M hM, e]
  exact fderiv_comm (hF.contDiffAt (hU.mem_nhds h1)) L M ((hM 1).trans (Matrix.one_mul X))
    ((hL 1).trans (Matrix.one_mul Y)) (congrArg₂ (· - ·) (hL X) (hM Y))

theorem derived_action_bracket : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ X Y, PI.UpqRep.InLieHpk k r X → PI.UpqRep.InLieHpk k r Y → ∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsig (k := k) (r := r) R.σ Y v) - PI.UpqRep.dsig (k := k) (r := r) R.σ Y (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (X * Y - Y * X) v :=
  fun _ _ _ _ _ _ hR _ _ hX hY _ hv => dsig_bracket hR.2 hX hY hv

end GlobalTheory.DerivedBracket
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnitBoxWords

open PI.UpqRep GlobalTheory.DerivedAction

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}

def lieSubspace (k r : ℕ) : Submodule ℝ (Mx k r) where
  carrier := {X | InLieHpk k r X}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq, InLieHpk] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp [InLieHpk]
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq, InLieHpk] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem exists_box_generators (k r : ℕ) : ∃ (J : Type) (_ : Fintype J) (Z : J → Mx k r),
    (∀ j, InLieHpk k r (Z j)) ∧ ∀ Y, B.unitLie k r Y → ∃ c : J → ℝ, (∀ j, |c j| ≤ 1) ∧ Y = ∑ j, c j • Z j := by
  obtain ⟨P, hP⟩ := (lieSubspace k r).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let n := Fin (2 * r + k + 1)
  let E : (n × n) ⊕ (n × n) → Mx k r :=
    Sum.elim (fun p => Matrix.single p.1 p.2 1) (fun p => Matrix.single p.1 p.2 Complex.I)
  refine ⟨(n × n) ⊕ (n × n), inferInstance, fun j => (P (E j)).1, fun j => (P (E j)).2, fun Y hY => ?_⟩
  let c : (n × n) ⊕ (n × n) → ℝ := Sum.elim (fun p => (Y p.1 p.2).re) (fun p => (Y p.1 p.2).im)
  refine ⟨c, ?_, ?_⟩
  · rintro (p | p)
    · exact (Complex.abs_re_le_norm _).trans (hY.2 _ _)
    · exact (Complex.abs_im_le_norm _).trans (hY.2 _ _)
  · have h1 : Y = ∑ j, c j • E j := by
      rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, Fintype.sum_prod_type]
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [c, E, Sum.elim_inl, Sum.elim_inr, Matrix.smul_single, ← Matrix.single_add]
      congr 1
      simp [Complex.real_smul]
    have hYL : Y ∈ lieSubspace k r := hY.1
    have h2 : (P Y).1 = Y := by
      have := LinearMap.congr_fun hP ⟨Y, hYL⟩
      exact congrArg Subtype.val this
    calc Y = (P Y).1 := h2.symm
      _ = (P (∑ j, c j • E j)).1 := by rw [← h1]
      _ = _ := by simp [map_sum]

theorem dsig_sum_letter {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {J : Type} [Fintype J] {Z : J → Mx k r} (hZ : ∀ j, InLieHpk k r (Z j)) (c : J → ℝ) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ (∑ j, c j • Z j) v = ∑ j, (c j : ℂ) • dsig (k := k) (r := r) σ (Z j) v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  have hm : (∑ j, c j • Z j) ∈ lieSubspace k r :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hZ j)

  rw [(hL _ hm).1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, (hL _ (hZ j)).1, Complex.coe_smul]

theorem dsig_sum_vec (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {v : ι → R.H} (hv : ∀ i, v i ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dsig (k := k) (r := r) R.σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dsig_zero]
  | insert a s ha ih =>
    have h1 : c a • v a ∈ R.smSub := R.smSub.smul_mem _ (hv a)
    have h2 : ∑ i ∈ s, c i • v i ∈ R.smSub := R.smSub.sum_mem fun i _ => R.smSub.smul_mem _ (hv i)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dsig_add hX h1 h2, dsig_smul hX _ (hv a), ih]

theorem box_words_fintype (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDS ε mu) {x : R.H} (hx : x ∈ R.TK) (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (xs : ι → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r),
      (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : ι → ℝ, (∀ i, |co i| ≤ 1) ∧
        dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  obtain ⟨J, _, Z, hZ, hbox⟩ := exists_box_generators k r
  have h0 : InLieHpk k r (0 : Mx k r) := (lieSubspace k r).zero_mem
  induction m with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ => x, fun _ => hx, fun a _ hl => ⟨fun _ => 1, by simp, ?_⟩⟩
    obtain rfl : a = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    simp [dsigW]
  | succ m ih =>
    obtain ⟨ι, _, xs, hxs, h⟩ := ih
    refine ⟨Unit ⊕ (J × ι), inferInstance,
      Sum.elim (fun _ => x) (fun p => dsig (k := k) (r := r) R.σ (Z p.1) (xs p.2)), ?_, ?_⟩
    · rintro (p | p)
      · exact hx
      · exact (dsig_TK hK R hR (hZ p.1) _ (hxs p.2)).2
    · intro a ha hl
      cases a with
      | nil =>
        refine ⟨Sum.elim (fun _ => 1) (fun _ => 0), ?_, ?_⟩
        · rintro (p | p) <;> simp
        · simp [dsigW, Fintype.sum_sum_type]
      | cons Y a =>
        have hY := ha Y (by simp)
        obtain ⟨co, hco, e⟩ := h a (fun Y hY => ha Y (by simp [hY])) (by simpa using hl)
        obtain ⟨c, hc, eY⟩ := hbox Y hY
        have hsm : ∀ i, xs i ∈ R.sm := fun i => (dsig_TK hK R hR h0 _ (hxs i)).1
        refine ⟨Sum.elim (fun _ => 0) (fun p => co p.2 * c p.1), ?_, ?_⟩
        · rintro (p | p)
          · simp
          · simp only [Sum.elim_inr, abs_mul]
            exact mul_le_one₀ (hco _) (abs_nonneg _) (hc _)
        · have hYL : InLieHpk k r Y := hY.1
          show dsig (k := k) (r := r) R.σ Y (dsigW (k := k) (r := r) R.σ a x) = _
          rw [e, dsig_sum_vec R hYL _ _ hsm, Fintype.sum_sum_type, Fintype.sum_prod_type_right]
          simp only [Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, zero_add]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [eY, dsig_sum_letter hZ c (hsm i), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul, Complex.ofReal_mul]

theorem box_words : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ x ∈ R.TK, ∀ m : ℕ, ∃ (M : ℕ) (xs : Fin M → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : Fin M → ℝ, (∀ i, |co i| ≤ 1) ∧ PI.UpqRep.dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  intro hK k r ε mu R hR x hx m
  obtain ⟨ι, _, xs, hxs, h⟩ := box_words_fintype hK R hR hx m
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, xs ∘ e, fun i => hxs _, fun a ha hl => ?_⟩
  obtain ⟨co, hco, h'⟩ := h a ha hl
  refine ⟨co ∘ e, fun i => hco _, ?_⟩
  rw [h', ← e.sum_comp]
  rfl

end GlobalTheory.UnitBoxWords
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoeffDeriv

open GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def coefL (R : Rep k r) (x : R.H) (X : V) : R.H →L[ℝ] V :=
  ((innerSL ℂ x).smulRight X).restrictScalars ℝ

theorem coefL_apply (x w : R.H) (X : V) : coefL R x X w = ⟪x, w⟫_ℂ • X := rfl

theorem dsigW_smooth (hR : R.IsDS ε mu) {y : R.H} (hy : y ∈ R.sm) (b : List (Mx k r))
    (hb : ∀ Y ∈ b, B.inLie k r Y) : PI.UpqRep.dsigW (k := k) (r := r) R.σ b y ∈ R.sm := by
  induction b with
  | nil => exact hy
  | cons Y b ih =>
    exact dsig_smooth hR.2 (hb Y (by simp)) (ih fun Z hZ => hb Z (by simp [hZ]))

theorem right_step (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) (X : V) (F : Mx k r → V) (x : R.H) {y : R.H}
    (hy : y ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    deriv (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      ⟪x, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ Y y)⟫_ℂ • X := by
  obtain ⟨hmul, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  have h := (coefL R x X).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_apply (σ := R.σ) hY hy (R.σ g))
  rw [← coefL_apply, ← h.deriv]
  congr 1
  funext t
  have he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := exp_mem hY t
  rw [hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg he), hmul g hg _ he]
  rfl

theorem left_step (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) (X : V) (F : Mx k r → V) {x : R.H} (y : R.H)
    (hx : x ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    B.LdV Y F g = ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ Y x, R.σ g y⟫_ℂ • X := by
  obtain ⟨hmul, hone, hinner, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  have h1 := (hasDerivAt_dsig (σ := R.σ) hY hx).inner ℂ (hasDerivAt_const (0 : ℝ) (R.σ g y))
  simp only [inner_zero_right, zero_add] at h1
  have h := h1.smul_const X
  unfold B.LdV
  rw [← h.deriv]
  congr 1
  funext t
  have he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := exp_mem hY t
  have he' : NormedSpace.exp (-((t : ℂ) • Y)) ∈ GG k r := by
    have := exp_mem hY (-t)
    rwa [Complex.ofReal_neg, neg_smul] at this
  have hee : NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp (-((t : ℂ) • Y)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Y)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  rw [hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul he' hg), hmul _ he' g hg, ← hinner _ he, ← hmul _ he _ he', hee, hone]

theorem coeff_dLR : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : V) (F : Mx k r → V), R.IsDS ε mu → ∀ x ∈ R.sm, ∀ y ∈ R.sm, (∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) → B.CkOn ⊤ (B.GV k r) F ∧ ∀ a b : List (Mx k r), (∀ Y ∈ a, B.inLie k r Y) → (∀ Y ∈ b, B.inLie k r Y) → ∀ g ∈ GG k r, B.dLR a b F g = ⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
  intro hK k r ε mu R V _ _ X F hR x hx y hy hF
  refine ⟨fun g₀ hg₀ => ?_, fun a b ha hb => ?_⟩
  · obtain ⟨U, G, hU, hgU, hG, hfG⟩ := hy g₀ hg₀
    refine ⟨U, fun g => coefL R x X (G g), hU, hgU, (coefL R x X).contDiff.comp_contDiffOn hG, ?_⟩
    intro g hg hgG
    have e : R.σ g y = G g := hfG g hg hgG
    rw [hF g hgG, e]
    rfl
  · have hRw : ∀ g ∈ GG k r, B.Rw b F g = ⟪x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
      induction b with
      | nil => exact hF
      | cons Y b ih =>
        have hb' : ∀ Z ∈ b, B.inLie k r Z := fun Z hZ => hb Z (by simp [hZ])
        intro g hg
        exact right_step hK hR X _ x (dsigW_smooth hR hy b hb') (ih hb') (hb Y (by simp)) g hg
    induction a with
    | nil => exact hRw
    | cons Y a ih =>
      have ha' : ∀ Z ∈ a, B.inLie k r Z := fun Z hZ => ha Z (by simp [hZ])
      intro g hg
      exact left_step hK hR X _ _ (dsigW_smooth hR hx a ha') (ih ha') (ha Y (by simp)) g hg

end GlobalTheory.CoeffDeriv
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnipotentElement

open Formalism.HermitianLatticeCounting.ExpansionTerms

theorem exp_of_cube_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A * A * A = 0) (t : ℂ) :
    NormedSpace.exp (t • A) = 1 + t • A + (t ^ 2 / 2) • (A * A) := by
  have h3 : A ^ 3 = 0 := by rw [pow_three']; exact h
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_pow, smul_smul, pow_two A]
    simp [Nat.factorial, div_eq_inv_mul]
  · intro b hb
    have hb3 : 3 ≤ b := by simpa using hb
    rw [smul_pow, pow_eq_zero_of_le hb3 h3, smul_zero, smul_zero]

theorem ymat_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (e v : Fin n → ℂ) :
    rankTwoSkewMatrix H e v = vecMulVec e (star v) * H - vecMulVec v (star e) * H := by
  ext i j
  simp [rankTwoSkewMatrix, Formalism.QuantumDeterminants.herm, Matrix.mul_apply, vecMulVec_apply, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm]

theorem ymat_skew {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (e v : Fin n → ℂ) :
    (rankTwoSkewMatrix H e v)ᴴ * H + H * rankTwoSkewMatrix H e v = 0 := by
  rw [ymat_eq, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hH, conjTranspose_vecMulVec,
    conjTranspose_vecMulVec, star_star, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Matrix.mul_assoc]
  abel

theorem form_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (x y : EuclideanSpace ℂ (Fin n)) :
    majorantHermitianForm (Matrix.toEuclideanLin H) x y = Formalism.QuantumDeterminants.herm H x.ofLp y.ofLp := by
  unfold majorantHermitianForm Formalism.QuantumDeterminants.herm
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  show star (H *ᵥ y.ofLp) ⬝ᵥ x.ofLp = _
  rw [star_mulVec, hH, dotProduct_mulVec]

theorem isTheta {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) :
    IsSelfAdjointInvolution (Matrix.toEuclideanLin H) := by
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · apply WithLp.ofLp_injective
    show H *ᵥ (H *ᵥ x.ofLp) = x.ofLp
    rw [mulVec_mulVec, hHH, one_mulVec]
  · exact (Matrix.isSymmetric_toEuclideanLin_iff.2 hH) x y

theorem ymat_hs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (e v : EuclideanSpace ℂ (Fin n)) :
    ∑ i, ∑ j, ‖rankTwoSkewMatrix H e.ofLp v.ofLp i j‖ ^ 2 ≤ 4 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := Formalism.HermitianLatticeCounting.P.gram_hilbert_schmidt_bound _ _ (isTheta H hH hHH) n (EuclideanSpace.basisFun (Fin n) ℂ) e v
  refine le_of_eq_of_le ?_ h
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [form_eq H hH, form_eq H hH, EuclideanSpace.basisFun_inner]
  simp [rankTwoSkewMatrix]

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm H (g *ᵥ x) (g *ᵥ y) = Formalism.QuantumDeterminants.herm H x y := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

theorem exists_element : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, ∀ a : Fin r, ∃ X : Mx k r, PI.UpqRep.InLieHpk k r X ∧ (∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ 4 * lenA k r z g a.castSucc ^ 2) ∧ ∀ t : ℝ, ∃ m ∈ Formalism.QuantumDeterminants.Nset k r, g * NormedSpace.exp ((t : ℂ) • X) = m * g ∧ Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m = Complex.exp (-(2 * (lenA k r z g a.succ : ℂ) * (t : ℂ)) * Complex.I) := by
  intro k r z hz hT g hg a
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hu : IsUnit g.det := GlobalTheory.TensLen.isUnit_det_of_unitary hHH hg
  have hHu : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := Matrix.isUnit_det_of_left_inverse hHH
  have hpos := (GlobalTheory.TensLen.lengths k r z hz hT g hg).2.2.1 a.succ
  obtain ⟨e', v', he, hen, hvn, hv0, hv1⟩ := Formalism.HermitianLatticeCounting.P.majorant_parameter_choice_holds _ _ (isTheta _ hH hHH) r
    (fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a hpos.ne'
  have hgg : ∀ x : Fin (2 * r + k + 1) → ℂ, g *ᵥ (g⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hgg' : ∀ x : Fin (2 * r + k + 1) → ℂ, g⁻¹ *ᵥ (g *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hform : ∀ b, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) (g *ᵥ v'.ofLp) =
      majorantHermitianForm (Matrix.toEuclideanLin (Formalism.QuantumDeterminants.Hpk k r))
        (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b)) v' := fun b => by
    rw [form_eq _ hH, ← herm_mulVec hg (WithLp.ofLp _) v'.ofLp, WithLp.ofLp_toLp, hgg]
  have hE : g *ᵥ e'.ofLp - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
      Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) := by
    have h1 := Submodule.mem_map_of_mem
      (f := (Matrix.mulVecLin g).comp (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap) he
    rw [Submodule.map_span, Set.image_image] at h1
    simpa [mulVec_sub, hgg, -mulVec_mulVec] using h1
  have hV0 : ∀ b, b ≤ a.castSucc →
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) (g *ᵥ v'.ofLp) = 0 := fun b hb => by
    rw [hform]; exact hv0 b hb
  have hV1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) (g *ᵥ v'.ofLp) =
      -Complex.I * (lenA k r z g a.succ : ℂ) := by
    rw [hform]; exact hv1
  obtain ⟨h3, -, hN⟩ := Formalism.HermitianLatticeCounting.P.nilpotent_model_computation_holds k r z hz a _ _ hE hV0
  have hpsi := Formalism.HermitianLatticeCounting.P.derivative_of_psi_holds k r z hz a _ _ 1 _ hE hV0 hV1
  have hAd := Formalism.HermitianLatticeCounting.P.matrix_adjoint_action_holds _ _ hHu g hg (g *ᵥ e'.ofLp) (g *ᵥ v'.ofLp)
  rw [hgg', hgg'] at hAd
  refine ⟨rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e'.ofLp v'.ofLp, ymat_skew _ hH _ _, ?_, fun t => ⟨_, (hN t).1, ?_, ?_⟩⟩
  · have h := ymat_hs _ hH hHH e' v'
    rw [hvn, hen, one_pow, mul_one] at h
    exact h
  · rw [← hAd, ← Matrix.smul_mul, ← Matrix.mul_smul,
      Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 hu), exp_of_cube_eq_zero _ h3,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
    rfl
  · simpa using hpsi t

end GlobalTheory.UnipotentElement
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (R : Rep k r) (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → (∀ v ∈ R.sm, v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun g => R.σ (Q⁻¹ * g * Q))) ∧ ∀ Y v, PI.DSInfCharCap.dsigC ε (fun g => R.σ (Q⁻¹ * g * Q)) Y v = R.dC (Q⁻¹ * Y * Q) v := by
  first | exact @GlobalTheory.CayleyTransport.smooth_and_dsigC_transport | exact GlobalTheory.CayleyTransport.smooth_and_dsigC_transport | (intros; apply GlobalTheory.CayleyTransport.smooth_and_dsigC_transport <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.derivedAction_discreteSeries_properties : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ X, PI.UpqRep.InLieHpk k r X → (∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧ HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) 0) ∧ (∀ v ∈ R.sm, ∀ g ∈ GG k r, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (g * X * g⁻¹) (R.σ g v)) ∧ (∀ v, R.KFin v → R.KFin (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) ∧ (∀ v ∈ R.TK, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.TK) ∧ (∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, PI.UpqRep.dsig (k := k) (r := r) R.σ X w⟫_ℂ) := by
  first | exact @GlobalTheory.DerivedAction.derived_action | exact GlobalTheory.DerivedAction.derived_action | (intros; apply GlobalTheory.DerivedAction.derived_action <;> assumption)
end
