module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d m n : ℕ}

def CZ (a : Fin m → Pt k n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

theorem CZ.hasSubst {a : Fin m → Pt k n d} (ha : CZ a) : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

theorem ev_add {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f + g) = ev a f + ev a g := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, h, h, map_add (f := _)]

theorem ev_mul {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f * g) = ev a f * ev a g := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, h, h, map_mul]

def evHom {a : Fin m → Pt k n d} (ha : CZ a) : PS k m d →+* PS k n d :=
  (substAlgHom ha.hasSubst).toRingHom

theorem evHom_apply {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : evHom ha f = ev a f := by
  exact congrFun (MvPowerSeries.coe_substAlgHom ha.hasSubst) f

theorem ev_sub {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f - g) = ev a f - ev a g := by
  rw [← evHom_apply ha, ← evHom_apply ha, ← evHom_apply ha, map_sub]

theorem ev_neg {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : ev a (-f) = -ev a f := by
  rw [← evHom_apply ha, ← evHom_apply ha, map_neg]

theorem ev_sum {a : Fin m → Pt k n d} (ha : CZ a) {ι : Type} (s : Finset ι) (f : ι → PS k m d) :
    ev a (∑ x ∈ s, f x) = ∑ x ∈ s, ev a (f x) := by

  rw [← evHom_apply ha, map_sum]
  exact Finset.sum_congr rfl (fun x _ => evHom_apply ha (f x))

theorem ev_C {a : Fin m → Pt k n d} (ha : CZ a) (c : k) : ev a (C c : PS k m d) = C c := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, show (C c : PS k m d) = algebraMap k (PS k m d) c from rfl, AlgHom.commutes]
  rfl

theorem ev_X {a : Fin m → Pt k n d} (ha : CZ a) (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS k m d) = a j i :=
  MvPowerSeries.subst_X ha.hasSubst (j, i)

theorem ev_zero' {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  rw [← evHom_apply ha, map_zero]

theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : CZ a) {f : PS k m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf

theorem CZ.ev {a : Fin m → Pt k n d} (ha : CZ a) {l : ℕ} {b : Fin l → Pt k m d} (hb : CZ b) :
    CZ (fun j i => ev a (b j i)) := fun j i => constantCoeff_ev ha (hb j i)

theorem ev_ev {l : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) {b : Fin l → Pt k m d} (hb : CZ b) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  exact MvPowerSeries.subst_comp_subst_apply hb.hasSubst ha.hasSubst f

theorem ev_pt (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by
  show MvPowerSeries.subst (fun p : Fin m × Fin d => (X p : PS k m d)) f = f
  rw [show (fun p : Fin m × Fin d => (X p : PS k m d)) = X from rfl, MvPowerSeries.subst_self]
  rfl

theorem CZ.pt : CZ (fun j => pt k (n := n) d j) := fun j i => MvPowerSeries.constantCoeff_X _

open scoped MvPowerSeries.WithPiTopology in
theorem pderiv_ev {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d) :
    pderiv v (ev a f) = ∑ p : Fin m × Fin d, ev a (pderiv p f) * pderiv v (a p.1 p.2) := by
  classical
  let : UniformSpace k := ⊥
  let b : Fin m × Fin d → PS k n d := fun p => a p.1 p.2
  change pderiv v (subst b f) = ∑ p, subst b (pderiv p f) * pderiv v (b p)
  have hsubst : Continuous (subst b : PS k m d → PS k n d) := continuous_subst ha.hasSubst
  have hderiv {σ : Type} (i : σ) : Continuous (pderiv (R := k) i) := by
    apply continuous_pi
    intro e
    change Continuous (fun g => coeff e (pderiv i g))
    simp only [coeff_pderiv]
    exact (WithPiTopology.continuous_coeff k _).mul continuous_const
  refine congrFun (WithPiTopology.denseRange_toMvPowerSeries.equalizer
    (hderiv v |>.comp hsubst) (continuous_finsetSum _ fun p _ =>
      (hsubst.comp (hderiv p)).mul continuous_const) ?_) f
  funext q
  change pderiv v (subst b (q : PS k m d)) =
    ∑ p, subst b (pderiv p (q : PS k m d)) * pderiv v (b p)
  simp only [pderiv_coe, subst_coe]
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add q r hq hr => simp only [map_add, hq, hr, add_mul, Finset.sum_add_distrib]
  | mul_X q p hq =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hq, smul_eq_mul, smul_eq_mul,
      Finset.mul_sum]
    simp [Pi.single_apply, apply_ite (MvPolynomial.aeval b), add_mul, Finset.sum_add_distrib,
      mul_assoc]

theorem ev_zeroFam (f : PS k m d) : ev (fun _ _ => (0 : PS k n d)) f = C (constantCoeff f) := by
  classical
  have hz : CZ (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  ext e
  unfold ev
  rw [coeff_subst hz.hasSubst, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp) (zero_pow hp), map_zero, smul_zero]

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Dof
variable (F : Fin d → PS k 2 d) (v : Fin d → k)

theorem dof_add (f g : PS k 1 d) : Dof F v (f + g) = Dof F v f + Dof F v g := by
  unfold Dof
  simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem dof_zero : Dof F v (0 : PS k 1 d) = 0 := by
  simp [Dof]

theorem dof_C (a : k) : Dof F v (C a : PS k 1 d) = 0 := by
  simp [Dof]

theorem dof_mul (f g : PS k 1 d) : Dof F v (f * g) = Dof F v f * g + f * Dof F v g := by
  unfold Dof
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem dof_list_sum (L : List (PS k 1 d)) : Dof F v L.sum = (L.map (Dof F v)).sum := by
  induction L with
  | nil => simp [dof_zero]
  | cons a L ih => simp [dof_add, ih]

end Dof

section Words
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

def T (w : List ι) (A : PS k 1 d) : PS k 1 d := w.foldr (fun l g => Dof F (u l) g) A

theorem T_cons (l : ι) (w : List ι) (A : PS k 1 d) : T F u (l :: w) A = Dof F (u l) (T F u w A) := rfl

theorem T_append (w w' : List ι) (A : PS k 1 d) : T F u (w ++ w') A = T F u w (T F u w' A) := by
  simp [T, List.foldr_append]

def splits : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | l :: w => (splits w).map (fun p => (l :: p.1, p.2)) ++ (splits w).map (fun p => (p.1, l :: p.2))

theorem T_mul (w : List ι) (A B : PS k 1 d) :
    T F u w (A * B) = ((splits w).map (fun p => T F u p.1 A * T F u p.2 B)).sum := by
  induction w with
  | nil => simp [splits, T]
  | cons l w ih =>
    rw [T_cons, ih, dof_list_sum, List.map_map]
    simp only [splits, List.map_append, List.map_map, List.sum_append]
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    rw [dof_mul]
    rfl

end Words

end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.MV

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)

section Pair

variable {k : Type} [CommRing k] {σ : Type}

theorem coeff_iter_pderiv (i : σ) (c : ℕ) (g : MvPowerSeries σ k) (n : σ →₀ ℕ) :
    coeff n ((pderiv i)^[c] g) =
      coeff (n + c • Finsupp.single i 1) g * ((n i + 1).ascFactorial c : k) := by
  induction c generalizing n g with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv]
    have h1 : n + c • Finsupp.single i 1 + Finsupp.single i 1 = n + (c + 1) • Finsupp.single i 1 := by
      rw [add_smul, one_smul, add_assoc]
    have h2 : ((n + c • Finsupp.single i 1 : σ →₀ ℕ)) i = n i + c := by simp
    rw [h1, h2, Nat.ascFactorial_succ]
    push_cast
    ring

theorem coeff_fold {ι : Type} (cd : ι → σ) (hc : Function.Injective cd) (m : ι → ℕ) (f : MvPowerSeries σ k) :
    ∀ (L : List ι), L.Nodup → ∀ n : σ →₀ ℕ,
      coeff n (L.foldr (fun l g => (pderiv (cd l))^[m l] g) f) =
        coeff (n + (L.map fun l => m l • Finsupp.single (cd l) 1).sum) f *
          (L.map fun l => ((n (cd l) + 1).ascFactorial (m l) : k)).prod := by
  intro L
  induction L with
  | nil => intro _ n; simp
  | cons l L ih =>
    intro hnd n
    rw [List.nodup_cons] at hnd
    rw [List.foldr_cons, coeff_iter_pderiv, ih hnd.2]
    have hprod : (L.map fun l' => (((n + m l • Finsupp.single (cd l) 1 : σ →₀ ℕ) (cd l') + 1).ascFactorial (m l') : k)).prod
        = (L.map fun l' => ((n (cd l') + 1).ascFactorial (m l') : k)).prod := by
      congr 1
      apply List.map_congr_left
      intro l' hl'
      have hne : cd l ≠ cd l' := fun h => hnd.1 (by rw [hc h]; exact hl')
      simp [hne]
    rw [hprod, List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, add_assoc]
    ring

end Pair

section Pair2

variable {k : Type} [CommRing k]

end Pair2

end ReciprocityTheory.ChartRestriction.G.TB.MV
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

variable {k : Type} [CommRing k] [Algebra ℚ k]

theorem coeff_zero_of_scale {σ : Type} [Fintype σ] (w : σ → ℕ) (f : MvPowerSeries σ k)
    (h : subst ((fun s => (2 : k) ^ w s) • (X : σ → MvPowerSeries σ k)) f = (2 : k) • f) (n : σ →₀ ℕ)
    (hn : (∑ s, w s * n s) ≠ 1) : coeff n f = 0 := by
  have h2 := congrArg (coeff n) h
  rw [← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (fun s => by simp), map_smul, smul_eq_mul] at h2
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum] at h2
  have hr : ((2 : ℚ) ^ (∑ s, w s * n s) - 2) ≠ 0 := by
    intro h0
    apply hn
    have h3 : (2 : ℕ) ^ (∑ s, w s * n s) = 2 := by exact_mod_cast sub_eq_zero.1 h0
    exact Nat.pow_right_injective (le_refl 2) (h3.trans (pow_one 2).symm)
  have hk : algebraMap ℚ k ((2 : ℚ) ^ (∑ s, w s * n s) - 2) * coeff n f = 0 := by
    rw [map_sub, map_pow, map_ofNat]
    linear_combination h2
  calc coeff n f
      = algebraMap ℚ k (((2 : ℚ) ^ (∑ s, w s * n s) - 2)⁻¹ * ((2 : ℚ) ^ (∑ s, w s * n s) - 2))
          * coeff n f := by rw [inv_mul_cancel₀ hr, map_one, one_mul]
    _ = 0 := by rw [map_mul, mul_assoc, hk, mul_zero]

theorem hasSubst_pts {n m d : ℕ} (a : Fin m → Pt k n d) (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2

theorem ev_ev {n m l d : ℕ} (a : Fin m → Pt k n d) (b : Fin n → Pt k l d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k m d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by
  unfold ev
  exact MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f

theorem ev_X {n m d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m) (i : Fin d) :
    ev a (X (j, i) : PS k m d) = a j i := by
  unfold ev
  exact MvPowerSeries.subst_X (hasSubst_pts a ha) (j, i)

def AddLinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 1 d),
    ev (n := 2) ![pt k d 0 + pt k d 1] f = ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f →
      ∀ n : Fin 1 × Fin d →₀ ℕ, n.degree ≠ 1 → coeff n f = 0

theorem ev_pt {n d : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f := by
  have e : (fun p : Fin n × Fin d => pt k d p.1 p.2) = MvPowerSeries.X := by
    funext p
    rfl
  unfold ev
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem sum_degree {σ : Type} [Fintype σ] (n : σ →₀ ℕ) : n.degree = ∑ s, 1 * n s := by
  rw [Finsupp.degree_eq_sum]
  simp

theorem ev_add' {n m d : ℕ} (b : Fin m → Pt k n d) (hb : ∀ j i, constantCoeff (b j i) = 0) (f g : PS k m d) :
    ev b (f + g) = ev b f + ev b g := by
  unfold ev
  exact MvPowerSeries.subst_add (hasSubst_pts b hb) f g

theorem addition_linear : AddLinSt := by
  intro k _ _ d f hf n hn
  let b : Fin 2 → Pt k 1 d := ![pt k d 0, pt k d 0]
  have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by
    fin_cases j <;> simp [b, pt]
  have hA : ev b (ev (n := 2) ![pt k d 0 + pt k d 1] f)
      = ev (fun (j : Fin 1) i => (2 : k) ^ 1 • (X (j, i) : PS k 1 d)) f := by
    rw [ev_ev _ _ (fun j i => by fin_cases j; simp [pt]) hb0]
    congr 1
    funext j i
    fin_cases j
    simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]
  have hB : ∀ c : Fin 2, ev b (ev (n := 2) ![pt k d c] f) = f := by
    intro c
    calc ev b (ev (n := 2) ![pt k d c] f) = ev (fun j => pt k d j) f := by
          rw [ev_ev _ _ (fun j i => by fin_cases j; simp [pt]) hb0]
          congr 1
          funext j i
          fin_cases j
          fin_cases c <;> simp [b, pt, ev_X b hb0]
      _ = f := ev_pt f
  have h1 := congrArg (ev b) hf
  rw [ev_add' b hb0, hA, hB 0, hB 1] at h1
  refine coeff_zero_of_scale (fun _ => 1) f ?_ n ?_
  · rw [two_smul]
    exact h1
  · rw [← sum_degree]
    exact hn

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.GE

variable {k : Type} [CommRing k] {d : ℕ}

def dofCoef (F : Fin d → PS k 2 d) (v : Fin d → k) (j : Fin d) : PS k 1 d :=
  ∑ i : Fin d, C (v i) * ev (n := 1) ![pt k d 0, 0] (pderiv ((1 : Fin 2), i) (F j))

def dofD (F : Fin d → PS k 2 d) (v : Fin d → k) : Derivation k (PS k 1 d) (PS k 1 d) :=
  ∑ j : Fin d, dofCoef F v j • pderiv ((0 : Fin 1), j)

theorem dofD_apply (F : Fin d → PS k 2 d) (v : Fin d → k) (f : PS k 1 d) :
    dofD F v f = Dof F v f := by
  have h : ∀ (s : Finset (Fin d)) (D : Fin d → Derivation k (PS k 1 d) (PS k 1 d)),
      (∑ j ∈ s, D j) f = ∑ j ∈ s, D j f := by
    intro s D
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  rw [dofD, h]
  simp only [Derivation.smul_apply, smul_eq_mul, Dof, dofCoef]

theorem dof_add (F : Fin d → PS k 2 d) (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f + g) = Dof F v f + Dof F v g := by
  simp only [← dofD_apply, map_add (f := _)]

theorem dof_mul (F : Fin d → PS k 2 d) (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f * g) = f * Dof F v g + g * Dof F v f := by
  simp only [← dofD_apply, Derivation.leibniz, smul_eq_mul]

theorem dof_C (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) : Dof F v (C r) = 0 := by
  have hC : (C r : PS k 1 d) = r • (1 : PS k 1 d) := by
    rw [MvPowerSeries.smul_eq_C_mul, mul_one]
  rw [← dofD_apply, hC, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]

theorem dof_C_mul (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) (f : PS k 1 d) :
    Dof F v (C r * f) = C r * Dof F v f := by
  rw [dof_mul, dof_C, mul_zero, add_zero]

theorem dof_sum (F : Fin d → PS k 2 d) (v : Fin d → k) {α : Type} (s : Finset α) (f : α → PS k 1 d) :
    Dof F v (∑ a ∈ s, f a) = ∑ a ∈ s, Dof F v (f a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← dofD_apply, map_sum]

end ReciprocityTheory.ChartRestriction.G.TB.GE
end
end
