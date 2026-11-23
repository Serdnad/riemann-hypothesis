module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle005
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
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

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def QuadColDerivSt : Prop :=
  ∀ (k : Type) [CommRing k] (d n : ℕ) (β : Matrix (Fin d) (Fin d) k),
    constantCoeff (quadCol (n := n) β) = 0 ∧
    (∀ (u : Fin d → k) (b : Fin n), constantCoeff (dAdd u b (quadCol (n := n) β)) = 0) ∧
    ∀ (u v : Fin d → k) (b b' : Fin n), dAdd u b (dAdd v b' (quadCol (n := n) β)) =
      C (if b = b' then dotProduct u (β.mulVec v) + dotProduct v (β.mulVec u) else 0)

private theorem pderiv_X_eq_C_ite {k : Type} [CommRing k] {n d : ℕ} (p q : Fin n × Fin d) :
    MvPowerSeries.pderiv p (X q : PS k n d) = C (if q = p then (1 : k) else 0) := by
  classical
  rw [MvPowerSeries.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

private theorem pderiv_C_mul' {k : Type} [CommRing k] {n d : ℕ} (p : Fin n × Fin d) (a : k)
    (Y : PS k n d) : MvPowerSeries.pderiv p (C a * Y) = C a * MvPowerSeries.pderiv p Y := by
  rw [Derivation.leibniz, MvPowerSeries.pderiv_C, smul_zero, add_zero, smul_eq_mul]

private theorem pderiv_C_mul_X_mul_X {k : Type} [CommRing k] {n d : ℕ} (p q r : Fin n × Fin d) (a : k) :
    MvPowerSeries.pderiv p (C a * X q * X r : PS k n d) =
      C (a * (if r = p then 1 else 0)) * X q + C (a * (if q = p then 1 else 0)) * X r := by
  rw [Derivation.leibniz, pderiv_C_mul', pderiv_X_eq_C_ite, pderiv_X_eq_C_ite, smul_eq_mul, smul_eq_mul,
    map_mul, map_mul]
  ring

private theorem sum_quadratic_column_indicator_eq_dotProduct_mulVec {k : Type} [CommRing k] {d n : ℕ} (β : Matrix (Fin d) (Fin d) k)
    (u v : Fin d → k) (b b' : Fin n) :
    (∑ m : Fin d, ∑ j : Fin d, ∑ c : Fin n, ∑ i : Fin d, ∑ l : Fin d,
      (u m * (v j * (β i l * (if ((c, l) : Fin n × Fin d) = (b', j) then 1 else 0)) *
          (if ((c, i) : Fin n × Fin d) = (b, m) then 1 else 0)) +
        u m * (v j * (β i l * (if ((c, i) : Fin n × Fin d) = (b', j) then 1 else 0)) *
          (if ((c, l) : Fin n × Fin d) = (b, m) then 1 else 0)))) =
      if b = b' then dotProduct u (β.mulVec v) + dotProduct v (β.mulVec u) else 0 := by
  by_cases hb : b = b'
  · subst hb
    simp only [Prod.mk.injEq, ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_add_distrib, if_true]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hc : c = b
    · subst hc
      simp [Prod.mk.injEq, hb]
    · simp [Prod.mk.injEq, hc]

theorem quadratic_column_derivative : QuadColDerivSt := by
  intro k _ d n β
  classical
  refine ⟨?_, ?_, ?_⟩

  · simp [quadCol, map_sum]
  · intro u b

    simp only [dAdd, quadCol, map_sum, pderiv_C_mul_X_mul_X, pderiv_C_mul', map_add (f := _), map_mul,
    MvPowerSeries.constantCoeff_X, mul_zero, add_zero, Finset.sum_const_zero]
  · intro u v b b'


    simp only [dAdd, quadCol, map_sum, pderiv_C_mul_X_mul_X, pderiv_C_mul', map_add (f := _), Finset.mul_sum,
    mul_add, pderiv_X_eq_C_ite]
    simp only [← mul_assoc, ← map_mul]

    simp only [← map_add (f := _), ← map_sum]
    congr 1
    rw [← sum_quadratic_column_indicator_eq_dotProduct_mulVec β u v b b']
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun l _ => by ring

end ReciprocityTheory.ChartRestriction.G.TB
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

theorem constSt : ConstSt := by
  intro k _ d φ hφ g
  have ha : ∀ p : Fin 1 × Fin d, constantCoeff (![φ] p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    simpa using hφ j
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ![φ] p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have h0 : constantCoeff (e.prod fun s n => (![φ] s.1 s.2) ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
      rw [map_pow, ha p, zero_pow hp]
    rw [h0, smul_zero]

open scoped MvPowerSeries.WithPiTopology

open scoped MvPowerSeries.WithPiTopology in
theorem continuous_pderiv_disc {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => MvPowerSeries.pderiv i f) := by
  refine continuous_pi fun n => ?_
  have h : (fun f : MvPowerSeries σ R => (MvPowerSeries.pderiv i f) n) =
      (fun a : R => a * ((n i : R) + 1)) ∘ ⇑(MvPowerSeries.coeff (n + Finsupp.single i 1)) := by
    funext f
    exact MvPowerSeries.coeff_pderiv f n
  rw [h]
  exact continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff R _)

end ReciprocityTheory.ChartRestriction.G.TB
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem beta_sesquilinear : BetaSesqSt := by
  intro R _ d O _ _ k _ _ _ B a ξ η
  simp only [betaH, OactH, star_star, Finset.sum_sub_distrib]
  congr 1
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem betaH_smul_left {k : Type} [CommRing k] {d : ℕ} (c : k) (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k (c • ξ) η = c * betaH k ξ η := by
  simp only [betaH, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem betaH_smul_right {k : Type} [CommRing k] {d : ℕ} (c : k) (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k ξ (c • η) = c * betaH k ξ η := by
  simp only [betaH, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eigen_orthogonality : EigenOrthSt := by
  intro R _ d O _ _ k _ _ _ B χ χ' ξ η hξ hη ⟨a, ha⟩
  have h := beta_sesquilinear R d O k B a ξ η
  rw [hξ a, hη (star a), betaH_smul_left, betaH_smul_right] at h
  have h2 : (χ a - χ' (star a)) * betaH k ξ η = 0 := by rw [sub_mul, h, sub_self]
  exact ha.mul_right_eq_zero.mp h2

end ReciprocityTheory.ChartRestriction.G.TB
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.GE

def DofCommSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (u v : Fin d → k) (g : PS k 1 d),
    Dof (B.FK k) u (Dof (B.FK k) v g) = Dof (B.FK k) v (Dof (B.FK k) u g)

def WickExpSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (c : ι → ι → k) (P : MvPolynomial ι k) (q : PS k 1 d),
    (∀ l l', c l l' = c l' l) → constantCoeff q = 0 → (∀ l, constantCoeff (Dof F (u l) q) = 0) →
    (∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) →
    ∀ (t : k) (G : PS k 1 d),
      constantCoeff (DpolyOf F u P (G * FB.expS k (t • q))) =
        constantCoeff (DpolyOf F u (expSecond k c (t * algebraMap ℚ k (1 / 2)) P.totalDegree P) G)


end ReciprocityTheory.ChartRestriction.G.TB.GE
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB

theorem mvpoly_pderiv_comm {k σ : Type} [CommRing k] (i j : σ) (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅(MvPolynomial.pderiv i : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)), MvPolynomial.pderiv j⁆ =
      (0 : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X, Pi.single_apply,
      Pi.single_apply]
    split_ifs <;> simp
  have h' := congrArg (fun D => D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h'
  exact sub_eq_zero.mp h'

theorem harmSecond_holds : HarmSecondSt := by
  intro k _ T _ r cc isX hcc hX n c hc P hP
  classical
  set S : (Σ τ : T, Fin (r τ)) → (Σ τ : T, Fin (r τ)) → MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k :=
    fun l l' => ∑ b : Fin n, MvPolynomial.pderiv (l, b) (MvPolynomial.pderiv (l', b) P) with hS
  have hsymm : ∀ l l', S l l' = S l' l := by
    intro l l'
    simp only [hS]
    exact Finset.sum_congr rfl fun b _ => mvpoly_pderiv_comm _ _ _
  have hzero1 : ∀ l l' : (Σ τ : T, Fin (r τ)), isX l.1 → l'.1 = cc l.1 → S l l' = 0 := by
    rintro ⟨σ, i⟩ ⟨σ', i'⟩ hXσ h
    dsimp only at h hXσ
    subst h
    exact hP σ hXσ i i'
  have hzero : ∀ l l' : (Σ τ : T, Fin (r τ)), l'.1 = cc l.1 → S l l' = 0 := by
    intro l l' h
    rcases hX l.1 with h1 | h1
    · exact hzero1 l l' h1 h
    · rw [hsymm]
      refine hzero1 l' l (by rw [h]; exact h1) ?_
      rw [h, hcc]
  have hterm : ∀ l l', MvPolynomial.C (c l l') * S l l' = 0 := by
    intro l l'
    by_cases h : l'.1 = cc l.1
    · rw [hzero l l' h, mul_zero]
    · rw [hc l l' h, map_zero, zero_mul]
  unfold secondOrder
  simp_rw [Fintype.sum_prod_type]
  simp only [apply_ite MvPolynomial.C, ite_mul, map_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  apply Finset.sum_eq_zero
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l' _
  rw [← Finset.mul_sum]
  exact hterm l l'

end ReciprocityTheory.ChartRestriction.G.TB
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

theorem galois_twist_preserves_siegel_bound (hA : ExpAddZeroConstant) (hE : ConstantCoeffSubstitution) (hG : CanonicalGaugeDiffBiadditive) (hQ : QuadraticFormDerivatives)
    (hW : WickOperatorVanishing) : AdmissibilitySecond := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' w0 m ι _ u P hP f
  unfold FB.nabVal
  set a : Fin 2 → Pt k 1 d := ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] with hadef
  set q := ev (n := 1) a (h' - h) with hqdef
  have hbi := hG R d O k B h h' hh hh'
  obtain ⟨hq0, hq1, hq2⟩ := hQ R d O k B (h' - h) hbi w0
  have hac : ∀ j i, constantCoeff (a j i) = 0 := by
    intro j i
    fin_cases j
    · simp [hadef, pt]
    · show constantCoeff (ev (n := 1) ![pt k d 0] (B.actK k w0 i)) = 0
      rw [hE k d 1 1 ![pt k d 0] _ (fun j i => by fin_cases j; simp [pt])]
      simp only [FB.actK]
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, B.A.const, map_zero]
  have hs : HasSubst (fun p : Fin 2 × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => hac p.1 p.2
  have hL' : B.hL k h' w0 = B.hL k h w0 + q := by
    simp only [FB.hL, hqdef, ev]
    rw [subst_sub hs]
    ring
  have hh0 : constantCoeff h = 0 := by
    have h1 := hE k d 2 1 ![0, pt k d 0] h (fun j i => by fin_cases j <;> simp [pt])
    rw [hh.ax0] at h1
    simpa using h1.symm
  have hL0 : constantCoeff (B.hL k h w0) = 0 := by
    simp only [FB.hL]
    rw [hE k d 2 1 _ h hac, hh0]
  have hexp : FB.expS k ((m : k) • B.hL k h' w0) =
      FB.expS k ((m : k) • B.hL k h w0) * FB.expS k ((m : k) • q) := by
    rw [hL', smul_add]
    exact hA k 1 d _ _ (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hL0, mul_zero])
      (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq0, mul_zero])
  rw [hexp, ← mul_assoc]
  symm
  exact hW k d (B.FK k) ι u
    (fun l l' => dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))))
    P q (fun l l' => add_comm _ _) hq0 (fun l => hq1 (u l)) (fun l l' => hq2 (u l) (u l')) hP (m : k)
    (f * FB.expS k ((m : k) • B.hL k h w0))

end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)
  (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
  (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)

def TG (w : List ι) (A : S) : S := w.foldr (fun l g => D l g) A

include hadd in
theorem D_zero (l : ι) : D l 0 = 0 := by
  simpa using hadd l 0 0

include hadd in
theorem D_list_sum (l : ι) (L : List S) : D l L.sum = (L.map (D l)).sum := by
  induction L with
  | nil => simpa using D_zero D hadd l
  | cons a L ih => simp [hadd, ih]

theorem TG_append (w w' : List ι) (A : S) : TG D (w ++ w') A = TG D w (TG D w' A) := by
  simp only [TG, List.foldr_append]

include hadd in
theorem TG_add (w : List ι) (A B : S) : TG D w (A + B) = TG D w A + TG D w B := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    show D l (TG D w (A + B)) = D l (TG D w A) + D l (TG D w B)
    rw [ih, hadd]

include hadd hmul in
theorem TG_mul (w : List ι) (A B : S) :
    TG D w (A * B) = ((splits w).map (fun p => TG D p.1 A * TG D p.2 B)).sum := by
  induction w with
  | nil => simp [TG, splits]
  | cons l w ih =>
    have e : ∀ (v : List ι) (X : S), TG D (l :: v) X = D l (TG D v X) := fun _ _ => rfl
    rw [e, ih, D_list_sum D hadd]
    simp only [splits, List.map_append, List.sum_append, List.map_map, Function.comp_def, e, hmul,
      List.sum_map_add]

section Q
variable (e : S →+* k) (c : ι → ι → k) (q : S)
  (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))

include hadd hC hq2 in
theorem TG_q_long (w : List ι) (hw : 3 ≤ w.length) : TG D w q = 0 := by
  induction w with
  | nil => simp at hw
  | cons l w ih =>
    show D l (TG D w q) = 0
    rcases Nat.lt_or_ge w.length 3 with h | h
    · have h2 : w.length = 2 := by
        simp only [List.length_cons] at hw
        omega
      obtain ⟨y, z, rfl⟩ := List.length_eq_two.mp h2
      show D l (D y (D z q)) = 0
      rw [hq2, hC]
    · rw [ih h, D_zero D hadd]

variable (he : ∀ a, e (κ a) = a)

include hadd hC hq0 hq1 hq2 he in
theorem e_TG_q (b : List ι) : e (TG D b q) = ev2 c b := by
  match b with
  | [] => exact hq0
  | [x] => exact hq1 x
  | [x, y] =>
    show e (D x (D y q)) = c x y
    rw [hq2, he]
  | x :: y :: z :: r =>
    rw [TG_q_long (D := D) (κ := κ) (hadd := hadd) (hC := hC) (c := c) (q := q) (hq2 := hq2)
      (w := x :: y :: z :: r) (by simp)]
    exact map_zero e

include hadd hmul hC hq0 hq1 hq2 he in
theorem e_TG_mul_q (w : List ι) (A : S) :
    e (TG D w (A * q)) = ((splits w).map (fun p => e (TG D p.1 A) * ev2 c p.2)).sum := by
  simp only [TG_mul (D := D) (hadd := hadd) (hmul := hmul), map_list_sum, List.map_map,
    Function.comp_def, map_mul, e_TG_q (D := D) (κ := κ) (hadd := hadd) (hC := hC) (e := e) (c := c)
      (q := q) (hq0 := hq0) (hq1 := hq1) (hq2 := hq2) (he := he)]

end Q

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
end
end
