module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.UnipRead

variable {E : Type} [Field E] {M c : ℕ}

def lv (M u : ℕ) : ℕ := if u < M then 1 else u - M + 1

theorem one_le_lv (M u : ℕ) : 1 ≤ lv M u := by unfold lv; split_ifs <;> omega

def Unip (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) : Prop :=
  ∀ u v : Fin (M + c), lv M v.1 ≤ lv M u.1 → x (Pi.single v 1) u = if u = v then 1 else 0

theorem apply_eq_sum (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) (w : Fin (M + c) → E) (l : Fin (M + c)) :
    x w l = ∑ v, w v * x (Pi.single v 1) l := by
  have hw : w = ∑ v, Pi.single v (w v) := (Finset.univ_sum_single w).symm
  conv_lhs => rw [hw]

  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h : (Pi.single v (w v) : Fin (M + c) → E) = w v • (Pi.single v (1 : E) : Fin (M + c) → E) := by
    ext j; simp [Pi.single_apply]
  rw [h, map_smul]
  simp

theorem eN_val (v : Fin (M + c)) : Loc.eN E (M + c) v.1 = Pi.single v 1 := by
  ext l; simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_out {j : ℕ} (h : ¬ j < M + c) : Loc.eN E (M + c) j = 0 := by
  ext l; simp only [Loc.eN, Pi.zero_apply]; rw [if_neg]; omega

theorem inX_apply (y : Fin M → E) (l : Fin (M + c)) :
    Loc.inX E M c y l = if h : l.1 < M then y ⟨l.1, h⟩ else 0 := by
  simp only [Loc.inX, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem col {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) (j : ℕ) (l : Fin (M + c))
    (hle : lv M j ≤ lv M l.1) : x (Loc.eN E (M + c) j) l = Loc.eN E (M + c) j l := by
  by_cases h : j < M + c
  · have := eN_val (E := E) (⟨j, h⟩ : Fin (M + c))
    simp only at this
    rw [this, hU l ⟨j, h⟩ hle]
    simp [Pi.single_apply]
  · rw [eN_out h, map_zero]

theorem r1cond_of_unip {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) : Loc.R1cond E M c x := by
  refine ⟨fun i w hw l hl => ?_, ?_, fun i l hl => ?_⟩
  · rw [apply_eq_sum]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v.1 < M + i
    · have hl' : ¬ l.1 < M + i := hl
      rw [hU l v (by unfold lv; split_ifs <;> omega), if_neg (by intro h; subst h; exact hl' hv), mul_zero]
    · rw [hw v hv, zero_mul]
  · ext l
    exact col hU M l (by have := one_le_lv M l.1; unfold lv at this ⊢; simp; omega)
  · have hl' : ¬ l.1 < M + i := hl
    show x _ l - _ = 0
    rw [col hU (M + i) l (by unfold lv; split_ifs <;> omega), sub_self]

theorem fixX_of_unip {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) : x ∈ Loc.fixX E M c := by
  intro y
  ext l
  rw [apply_eq_sum, Finset.sum_eq_single l]
  · by_cases hl : l.1 < M
    · rw [hU l l (le_refl _), if_pos rfl, mul_one]
    · simp [inX_apply, hl]
  · intro v _ hvl
    by_cases hv : v.1 < M
    · rw [hU l v (by have := one_le_lv M l.1; unfold lv; rw [if_pos hv]; exact this), if_neg (Ne.symm hvl), mul_zero]
    · rw [inX_apply, dite_eq_right hv, zero_mul]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem unip_of {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hR : Loc.R1cond E M c x)
    (hX : x ∈ Loc.fixX E M c) : Unip x := by
  intro u v hle
  by_cases hv : v.1 < M
  · have hs : (Pi.single v 1 : Fin (M + c) → E) = Loc.inX E M c (Pi.single ⟨v.1, hv⟩ 1) := by
      ext l; rw [inX_apply]; split_ifs with h
      · simp [Pi.single_apply, Fin.ext_iff]
      · simp [Pi.single_apply, Fin.ext_iff]; omega
    rw [hs, hX, ← hs]
    simp [Pi.single_apply]
  · have hj : M + (v.1 - M) = v.1 := by omega
    by_cases hu : u.1 < M + (v.1 - M)
    · have hvM : v.1 = M := by
        unfold lv at hle; split_ifs at hle <;> omega
      have h2 := congrFun hR.2.1 u
      have h4 := eN_val (E := E) v
      rw [hvM] at h4
      rw [h4] at h2
      rw [h2]; simp [Pi.single_apply]
    · have h3 := hR.2.2 (v.1 - M) u hu
      rw [hj, eN_val] at h3
      have h3' : x (Pi.single v 1) u - (Pi.single v 1 : Fin (M + c) → E) u = 0 := h3
      rw [sub_eq_zero] at h3'
      rw [h3']; simp [Pi.single_apply]

section Read
variable {k : Type} [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
  (e : A ⊕ Fin c ≃ Fin (M + c)) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem lev_eq (s : A ⊕ Fin c) : lev 1 s = lv M (e s).1 := by
  rcases s with a | i
  · have := eX_lt e rfl he a
    simp [lev, lv, this]
  · simp only [lev, Sum.elim_inr, lv, he i]
    split_ifs <;> omega


include he in
theorem inN_iff (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) : InN 1 (locHom ι e x) ↔ Unip x := by
  have hval : ∀ r s, (locHom ι e x).val r s = ι (x (Pi.single (e s) 1) (e r)) := fun r s => rfl
  have hent : ∀ (a : E) (r s : A ⊕ Fin c),
      ι a = (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k) r s ↔ a = if e r = e s then 1 else 0 := by
    intro a r s
    rw [Matrix.one_apply]
    by_cases h : r = s
    · simp [h, map_eq_one_iff ι ι.injective]
    · simp [h, e.injective.eq_iff]
  constructor
  · intro h u v hle
    have := h (e.symm u) (e.symm v) (by rw [lev_eq e he, lev_eq e he]; simpa using hle)
    rw [hval, hent] at this
    simpa using this
  · intro h r s hle
    rw [hval, hent]
    rw [lev_eq e he, lev_eq e he] at hle
    exact h (e r) (e s) hle

end Read

theorem mem_N1_iff_local_hom : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
    (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) →
    ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1 := by
  intro E k _ _ ι A _ _ M c c' e hcc he x
  subst hcc
  rw [Model.mem_N_iff, inN_iff ι e he]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact unip_of h1 h2
  · intro h
    have hN : locHom ι e x ∈ N k A c' 1 := Model.mem_N_iff.2 ((inN_iff ι e he x).2 h)
    have hinv : Unip x⁻¹ := by
      rw [← inN_iff ι e he, map_inv]
      exact Model.mem_N_iff.1 (inv_mem hN)
    exact ⟨⟨r1cond_of_unip h, r1cond_of_unip hinv⟩, fixX_of_unip h⟩

end GlobalTheory.UnipRead
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem GlobalTheory.denseGL_completion : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M e y V hV hy
  haveI : T2Space k := by
    rw [t2Space_iff_disjoint_nhds]
    intro a b hab
    have hne : valuation k (a - b) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hab)
    let γ : (ValueGroupWithZero k)ˣ := Units.mk0 _ hne
    rw [Filter.disjoint_iff]
    refine ⟨{z | valuation k (z - a) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩,
      {z | valuation k (z - b) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h := Valuation.map_sub_lt _ (show valuation k (z - b) < γ from hz2)
      (show valuation k (z - a) < γ from hz1)
    have e : (z - b) - (z - a) = a - b := by ring
    rw [e, Units.val_mk0] at h
    exact lt_irrefl _ h
  let φ : Matrix A A k → Matrix A A k × (Matrix A A k)ᵐᵒᵖ := fun m => (m, MulOpposite.op m⁻¹)
  have hφ : ∀ g : GL A k, φ g.val = Units.embedProduct _ g := by
    intro g
    refine Prod.ext rfl ?_
    simp [φ, Matrix.coe_units_inv]
  obtain ⟨W, hW, rfl⟩ := (Units.isInducing_embedProduct (M := Matrix A A k)).isOpen_iff.1 hV
  have hdet : y.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hinv : ContinuousAt (fun m : Matrix A A k => m⁻¹) y.val := by
    have h1 : (fun m : Matrix A A k => m⁻¹) = fun m => (m.det)⁻¹ • m.adjugate := by
      funext m; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    exact ContinuousAt.smul ((continuousAt_inv₀ hdet).comp (continuous_id.matrix_det).continuousAt)
      (continuous_id.matrix_adjugate).continuousAt
  have hφc : ContinuousAt φ y.val :=
    ContinuousAt.prodMk continuousAt_id (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hU : φ ⁻¹' W ∩ {m : Matrix A A k | m.det ≠ 0} ∈ nhds y.val := by
    refine Filter.inter_mem (hφc.preimage_mem_nhds (hW.mem_nhds ?_)) ?_
    · rw [hφ]; exact hy
    · exact (isOpen_compl_singleton.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hD : DenseRange (fun m : Matrix A A E => m.map ι) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
  obtain ⟨_, ⟨m', rfl⟩, hm'W, hm'd⟩ := Dense.inter_nhds_nonempty hD hU
  have hm'u : IsUnit m'.det := by
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply hm'd
    show (m'.map ι).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  let n : Matrix (Fin M) (Fin M) E := m'.submatrix e.symm e.symm
  have hn : IsUnit n.det := by
    simpa [n, Matrix.det_submatrix_equiv_self] using hm'u
  refine ⟨Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn), ?_⟩
  show Units.embedProduct _ _ ∈ W
  rw [← hφ, locHom_val, GlobalTheory.SymBridge.toLoc_eq_map_toMatrix']
  have h2 : LinearMap.toMatrix' (Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn)).toLinearMap = n := by
    exact LinearMap.toMatrix'_toLin' n
  rw [h2]
  have h3 : n.submatrix e e = m' := by
    ext i j; simp [n]
  rw [h3]
  exact hm'W
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.StabRead

variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
  {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}

theorem mem_stdAt_iff_int (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (v : Sp E M) :
    v ∈ stdAt E M P ↔ ∀ i, ι (v i) ∈ 𝒪[k] := by
  rw [GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.mem_stdAt]
  exact forall_congr' fun i => (hι _).symm

theorem single_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (m : Fin M) :
    (Pi.single m 1 : Sp E M) ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι]
  intro i
  rw [Pi.single_apply]
  split_ifs
  · rw [map_one]; exact Subring.one_mem _
  · rw [map_zero]; exact Subring.zero_mem _

theorem map_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (y : Sp E M ≃ₗ[E] Sp E M)
    (hy : ∀ i m, ι (y (Pi.single m 1) i) ∈ 𝒪[k]) {v : Sp E M} (hv : v ∈ stdAt E M P) : y v ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι] at hv ⊢
  intro i
  have e : y v = LinearMap.toMatrix' (y : Sp E M →ₗ[E] Sp E M) *ᵥ v := (LinearMap.toMatrix'_mulVec _ v).symm
  rw [e]

  simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, map_sum, map_mul]
  exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hy i m) (hv m)

end GlobalTheory.VolBridge.StabRead


open GlobalTheory.VolBridge.StabRead in
theorem GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k)
    (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M)
    (x : Sp E M ≃ₗ[E] Sp E M) : x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ stabL E M (stdAt E M P) := inv_mem hx
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · change ι (x (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx _).2 (single_mem_stdAt hι _)) _
    · change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx' _).2 (single_mem_stdAt hι _)) _
  · rintro ⟨h1, h2⟩
    have i1 : ∀ i m, ι (x (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h1 (e.symm i) (e.symm m)
      change ι (x (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    have i2 : ∀ i m, ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h2 (e.symm i) (e.symm m)
      change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    intro v
    constructor
    · intro hv
      have h := map_mem_stdAt hι _ i2 hv
      have ev : (x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (x v) = v := x.symm_apply_apply v
      rwa [ev] at h
    · exact map_mem_stdAt hι x i1
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.RankOneMatrix

def stepAt (M : ℕ) {N : ℕ} (l : Fin N) : ℕ := if l.val < M then 1 else l.val - M + 1

variable {E : Type} [Field E] {M c : ℕ}

theorem eN_eq_single {N j : ℕ} (h : j < N) : Loc.eN E N j = Pi.single (⟨j, h⟩ : Fin N) 1 := by
  funext l
  simp only [Loc.eN, Pi.single_apply, Fin.ext_iff, Fin.val_mk]

theorem eN_eq_zero {N j : ℕ} (h : N ≤ j) : Loc.eN E N j = 0 := by
  funext l
  have : l.val ≠ j := by have := l.isLt; omega
  simp [Loc.eN, this]

theorem mem_Ufl {v : Sp E (M + c)} {i : ℕ} :
    v ∈ Loc.Ufl E M c i ↔ ∀ l : Fin (M + c), M + i ≤ l.val → v l = 0 := by
  show (∀ l : Fin (M + c), l.1 ∉ {l | l < M + i} → v l = 0) ↔ _
  simp only [Set.mem_setOf_eq, not_lt]

def ColCond (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : Prop :=
  ∀ l m : Fin (M + c), stepAt M m ≤ stepAt M l → (M ≤ l.val ∨ M ≤ m.val) →
    x (Pi.single m 1) l = (Pi.single m 1 : Sp E (M + c)) l

theorem colCond_of_R1cond {x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)} (h : Loc.R1cond E M c x) : ColCond x := by
  intro l m hlm hM
  by_cases hm : m.val < M
  · have hl : M ≤ l.val := hM.resolve_right (by omega)
    have hv : (Pi.single m 1 : Sp E (M + c)) ∈ Loc.Ufl E M c 0 := by
      rw [mem_Ufl]
      intro l' hl'
      have : l' ≠ m := by rintro rfl; omega
      simp [Pi.single_apply, this]
    have h1 := (mem_Ufl.1 (h.1 0 _ hv)) l (by omega)
    have hne : l ≠ m := by rintro rfl; omega
    rw [h1]
    simp [Pi.single_apply, hne]
  · obtain ⟨j, hj⟩ : ∃ j, m.val = M + j := ⟨m.val - M, by omega⟩
    have hsingle : (Pi.single m 1 : Sp E (M + c)) = Loc.eN E (M + c) (M + j) := by
      rw [eN_eq_single (by omega : M + j < M + c)]
      congr 1
      exact Fin.ext hj
    by_cases hl : l.val < M
    · have hj0 : j = 0 := by
        simp only [stepAt, hl, hm, if_true, if_false] at hlm
        omega
      subst hj0
      rw [hsingle, add_zero, h.2.1]
    · have hjl : M + j ≤ l.val := by
        simp only [stepAt, hl, hm, if_false] at hlm
        omega
      have h3 := (mem_Ufl.1 (h.2.2 j)) l hjl
      rw [Pi.sub_apply, sub_eq_zero, ← hsingle] at h3
      exact h3

theorem R1cond_of_colCond {x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)} (h : ColCond x) : Loc.R1cond E M c x := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [mem_Ufl] at hv ⊢
    intro l hl
    have hv' : v = ∑ m, v m • (Pi.single m 1 : Sp E (M + c)) := by
      funext t
      simp [Finset.sum_apply, Pi.single_apply]

    rw [hv', map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : M + i ≤ m.val
    · rw [hv m hm, zero_mul]
    · have hne : l ≠ m := by rintro rfl; omega
      rw [h l m (by simp only [stepAt]; split_ifs <;> omega) (Or.inl (by omega))]
      simp [Pi.single_apply, hne]
  · by_cases hc : M < M + c
    · rw [eN_eq_single hc]
      funext l
      exact h l _ (by simp only [stepAt, Fin.val_mk]; split_ifs <;> omega) (Or.inr le_rfl)
    · rw [eN_eq_zero (by omega), map_zero]
  · by_cases hc : M + i < M + c
    · rw [mem_Ufl, eN_eq_single hc]
      intro l hl
      rw [Pi.sub_apply, h l _ (by simp only [stepAt, Fin.val_mk]; split_ifs <;> omega) (Or.inr (by simp)), sub_self]
    · rw [eN_eq_zero (by omega), map_zero, sub_zero]
      exact zero_mem _

theorem R1cond_iff_colCond (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : Loc.R1cond E M c x ↔ ColCond x :=
  ⟨colCond_of_R1cond, R1cond_of_colCond⟩

section Matrix

variable {k : Type} [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
  (e : A ⊕ Fin c ≃ Fin (M + c)) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem lev_eq_stepAt (r : A ⊕ Fin c) : lev 1 r = stepAt M (e r) := by
  rcases r with a | i
  · have := eX_lt e rfl he a
    simp [lev, stepAt, this]
  · have := he i
    simp only [lev, Sum.elim_inr, stepAt, this]
    split_ifs <;> omega

include he in
theorem isRight_iff (r : A ⊕ Fin c) : r.isRight ↔ M ≤ (e r).val := by
  rcases r with a | i
  · have := eX_lt e rfl he a
    simp only [Sum.isRight_inl, Bool.false_eq_true, false_iff, not_le]
    exact this
  · simp [he i]


include he in
theorem inR_locHom_iff (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : VolN.InR 1 (locHom ι e x) ↔ ColCond x := by
  have hval : ∀ r s, (locHom ι e x).val r s = ι (x (Pi.single (e s) 1) (e r)) := fun r s => rfl
  have hone : ∀ r s, (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k) r s = ι ((Pi.single (e s) (1 : E) : Sp E (M + c)) (e r)) := by
    intro r s
    simp only [Matrix.one_apply, Pi.single_apply, e.apply_eq_iff_eq]
    split_ifs <;> simp
  constructor
  · intro h l m hlm hM
    have := h (e.symm l) (e.symm m) (by rw [lev_eq_stepAt e he, lev_eq_stepAt e he]; simpa using hlm)
      (by rw [isRight_iff e he, isRight_iff e he]; simpa using hM)
    rw [hval, hone] at this
    simpa using ι.injective this
  · intro h r s hrs hR
    rw [hval, hone]
    congr 1
    apply h
    · rw [← lev_eq_stepAt e he, ← lev_eq_stepAt e he]; exact hrs
    · rw [← isRight_iff e he, ← isRight_iff e he]; exact hR

end Matrix

theorem mem_rationalFirstParabolic_iff_localGL_mem_rootExchange : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
    (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) →
    ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.R1 E M c' ↔ locHom ι e x ∈ R k A c 1 := by
  intro E k _ _ ι A _ _ M c c' e hcc he x
  subst hcc
  rw [VolN.mem_R_iff, ← map_inv, inR_locHom_iff ι e he, inR_locHom_iff ι e he,
    ← R1cond_iff_colCond, ← R1cond_iff_colCond]
  exact Iff.rfl

end GlobalTheory.RankOneMatrix
end
end
