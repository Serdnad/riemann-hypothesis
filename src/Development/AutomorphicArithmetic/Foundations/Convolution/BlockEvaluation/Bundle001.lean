module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Classical

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem totalDegree_aeval_le {σ : Type*} (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ 1) (p : Polynomial ℂ) :
    (Polynomial.aeval q p).totalDegree ≤ p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine totalDegree_finsetSum_le fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
  calc
    i * q.totalDegree ≤ i * 1 := Nat.mul_le_mul_left _ hq
    _ ≤ p.natDegree := by simpa using hi'

private theorem exists_fin_map (n : ℕ) (s : Multiset ℂ) (hs : s.card = n) :
    ∃ f : Fin n → ℂ, (Finset.univ : Finset (Fin n)).val.map f = s := by
  subst hs
  induction s using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get <;> simp

theorem UpperTheory.ConvolutionTheory.Ci.bdLem :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ κ' : Finset (Pl K)) (D D' d d' : ℕ) (R R' : PR K n),
      (Bd κ D d R → Bd κ' D' d' R' → Bd (κ ∪ κ') (D + D') (d + d') (R * R')) ∧ (∀ η m, Bd κ 0 m (chebP η m : PR K n)) ∧
      (κ ⊆ κ' → D ≤ D' → d ≤ d' → Bd κ D d R → Bd κ' D' d' R) ∧
      ∀ Λ : (K →+* ℂ) → Multiset ℂ, (∀ τ, (Λ τ).card = n) → ∃ L : Ix K n → ℂ, msOf L = Λ := by
  intro K _ _ n κ κ' D D' d d' R R'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, (totalDegree_mul _ _).trans (Nat.add_le_add h2 h2'), ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp (vars_mul R R' hx) with h | h
      · exact Finset.mem_union_left _ (h1 x h)
      · exact Finset.mem_union_right _ (h1' x h)
    · intro β
      rw [coeff_mul]
      exact totalDegree_finsetSum_le fun _ _ =>
        (totalDegree_mul _ _).trans (Nat.add_le_add (h3 _) (h3' _))
  · intro η m
    have hq : (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
      refine (totalDegree_mul _ _).trans ?_
      simp [totalDegree_X]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp [chebP, vars_C] at hx
    · simp [chebP]
    · intro β
      unfold chebP
      rw [coeff_C]
      split_ifs
      · refine (totalDegree_aeval_le _ hq _).trans ?_
        simp [Polynomial.Chebyshev.natDegree_T]
      · simp
  · rintro hκ hD hd ⟨h1, h2, h3⟩
    exact ⟨fun x hx => hκ (h1 x hx), h2.trans hD, fun β => (h3 β).trans hd⟩
  · intro Λ hΛ
    choose f hf using fun τ => exists_fin_map n (Λ τ) (hΛ τ)
    refine ⟨fun y => f y.1 y.2, ?_⟩
    funext τ
    exact hf τ
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem eval_powE {n : ℕ} (f : ℕ) (i : Fin n) (s : Multiset ℂ) (hs : s.card = n) :
    eval (fun j : Fin n => s.esymm (j + 1)) (powE f i) = (s.map (· ^ f)).esymm (i + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hs
      subst hl
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i)
      = expand f (esymm (Fin n) ℂ (i + 1)) := by
    rw [← esymmAlgHom_apply]
    have := congrArg Subtype.val
      ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
        ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)
    exact this
  have h2 := congrArg (aeval a) h1
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply] at h2
  have h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f := by
    apply MvPolynomial.algHom_ext
    intro r
    simp
  rw [h3] at h2
  simp only [aeval_esymm_eq_multiset_esymm] at h2
  rw [Multiset.map_map, ← coe_aeval_eq_eval]
  exact h2

theorem UpperTheory.ConvolutionTheory.Ci.valBc :
    ValBc := by
  classical
  intro F E _ _ _ _ _ n x Λ t P hP
  refine ⟨?_, ?_, ?_⟩
  · rw [← RingHom.comp_apply]
    refine hom_congr_vars (p₁ := P) (p₂ := P) ?_ ?_ rfl
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [val, bcPR]
      · rintro (_ | y)
        · simp [val, bcPR]
        · simp [val, bcPR, bcInf]
    · intro y hy _
      have h := eval_powE (resDeg F y.1) y.2 _ (hP y hy)
      simp only [val, bcPR, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]
      rw [hval, bcSat, ← h]
      have hc : ((eval fun o : Option (Ix F n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1)).comp C)
          = RingHom.id ℂ := by
        ext c
        simp
      rw [hc]
      rfl
  · intro y hy
    have h : bcPR F P = bind₁ (fun x : Pl E × Fin n =>
        (map C (rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)) : PR F n))
        (map (rename (Option.map fun x : Ix E n => (x.1.comp (algebraMap F E), x.2))).toRingHom P) := by
      rw [bind₁, aeval_def, eval₂_map]
      rfl
    rw [h] at hy
    obtain ⟨y', hy', hy2⟩ := mem_vars_bind₁ _ _ hy
    refine ⟨y', vars_map _ _ hy', ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_vars_rename _ _ (vars_map _ _ hy2)
    rfl
  · intro η m
    simp only [chebP, bcPR, eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Polynomial.aeval_algHom_apply]
    simp
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

private theorem prj_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) {v : H} (hv : v ∈ W) : prj W v = v := by
  unfold prj
  exact Submodule.starProjection_eq_self_iff.2 (W.le_topologicalClosure hv)

private theorem fixF_anti {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    {U U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (h : U' ≤ U) : fixF μ U ≤ fixF μ U' := by
  unfold fixF
  exact biInf_mono fun u hu => h hu

private theorem eig_fix {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : v ∈ V ∧ 𝔞.A v = (x : ℂ) • v ∧ v ∈ fixF μ 𝔞.U := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
  have h3 : 𝔞.A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 h2
  refine ⟨h1, h3, ?_⟩
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h4 := hA v
  rw [h3] at h4
  exact (Submodule.smul_mem_iff _ hx').1 h4

private theorem poly_ind {H σ ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ev : MvPolynomial σ (MvPolynomial ι ℂ) →+* (H →L[ℂ] H)) (f : MvPolynomial σ (MvPolynomial ι ℂ) →+* ℂ)
    (v : H) (s : Set σ) (h0 : ∀ c : ℂ, ev (C (C c)) v = f (C (C c)) • v)
    (h1 : ∀ i, ev (C (X i)) v = f (C (X i)) • v) (h2 : ∀ y ∈ s, ev (X y) v = f (X y) • v)
    (P : MvPolynomial σ (MvPolynomial ι ℂ)) (hP : ∀ y ∈ P.vars, y ∈ s) : ev P v = f P • v := by
  have hadd : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P + Q) v = f (P + Q) • v := by
    intro P Q hP hQ
    rw [map_add (f := _), map_add (f := _), ContinuousLinearMap.add_apply, hP, hQ, add_smul]
  have hmul : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P * Q) v = f (P * Q) • v := by
    intro P Q hP hQ
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hQ, map_smul, hP, smul_smul, mul_comm]
  have hC : ∀ c : MvPolynomial ι ℂ, ev (C c) v = f (C c) • v := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [C_add]; exact hadd _ _ hp hq
    | mul_X p i hp => rw [C_mul]; exact hmul _ _ hp (h1 i)
  have hm : P ∈ supported (MvPolynomial ι ℂ) s := mem_supported.2 fun y hy => hP y hy
  clear hP
  rw [supported_eq_adjoin_X] at hm
  induction hm using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact h2 y hy
  | algebraMap r => exact hC r
  | add p q _ _ hp hq => exact hadd _ _ hp hq
  | mul p q _ _ hp hq => exact hmul _ _ hp hq

private theorem eig_fixL {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) {w : Pl K} (hw : w ∉ 𝔞.S) :
    v ∈ V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) := by
  obtain ⟨h1, -, h2⟩ := eig_fix 𝔞 hA hx hv
  rw [Submodule.mem_inf, fixL]
  exact ⟨h1, fixF_anti μ (𝔞.max w hw) h2⟩

private theorem val_CC {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (c : ℂ) : val (n := n) x Λ t (C (C c)) = c := by simp [val]

private theorem val_none {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) : val (n := n) x Λ t (C (X none)) = x := by simp [val]

private theorem val_some {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (y : Ix K n) :
    val (n := n) x Λ t (C (X (some y))) = x * (Λ y.1).esymm (y.2 + 1) := by simp [val]

private theorem val_X {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (w : Pl K) (i : Fin n) :
    val (n := n) x Λ t (X (w, i)) = (t w).esymm (i + 1) := by simp [val, hval]

private theorem ev_val {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x)
    {ev : PR K n →+* (LL μ →L[ℂ] LL μ)} (hev : 𝔞.IsEv ev) {Λ : (K →+* ℂ) → Multiset ℂ} {t : Pl K → Multiset ℂ}
    (h : At μ 𝔞.S V Λ t) (P : PR K n) (hPv : ∀ y ∈ P.vars, y.1 ∉ 𝔞.S) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : ev P v = val x Λ t P • v := by
  obtain ⟨hvV, hAv, hvU⟩ := eig_fix 𝔞 hA hx hv
  obtain ⟨hI, hS⟩ := h
  have hO : Oinf μ 𝔞.ν 𝔞.a₀ v = (x : ℂ) • v := by
    rw [← hAv, Amp.A, ContinuousLinearMap.comp_apply, prj_self _ hvU]
  refine poly_ind ev (val x Λ t) v {y | y.1 ∉ 𝔞.S} (fun c => ?_) (fun o => ?_) (fun y hy => ?_) P hPv
  · rw [hev.const, val_CC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  · cases o with
    | none => rw [hev.amp, hAv, val_none]
    | some y =>
      obtain ⟨-, h1⟩ := hI y.1
      rw [hev.cen, Amp.Z, ContinuousLinearMap.comp_apply, prj_self _ hvU,
        h1 𝔞.ν 𝔞.a₀ 𝔞.smooth y.2 v hvV, hO, smul_smul, mul_comm, val_some]
  · obtain ⟨w, i⟩ := y
    obtain ⟨-, -, h1⟩ := hS w hy
    rw [hev.hecke w hy i, h1 i v (eig_fixL 𝔞 hA hx hv hy), val_X]

theorem UpperTheory.ConvolutionTheory.Ci.evVal :
    EvEx → ParEx → EvVal := by
  intro hE hP K _ _ _ n hn μ _ 𝔞 V x hx hV
  obtain ⟨-, -, hA, -⟩ := hE K n hn μ 𝔞
  obtain ⟨p1, p2, -⟩ := hP K n hn μ V hV
  refine ⟨fun hne => ?_, fun Λ t Λ' t' h h' => ?_, fun ev hev Λ t h P hPv v hv => ev_val 𝔞 hA hx hev h P hPv hv⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hB : ∀ w, ∃ B, w ∉ 𝔞.S → SSat μ V w B := by
      intro w
      by_cases hw : w ∈ 𝔞.S
      · exact ⟨0, fun h => absurd hw h⟩
      · obtain ⟨B, hB⟩ := (p2 w ((Submodule.ne_bot_iff _).2 ⟨v, eig_fixL 𝔞 hA hx hv hw, hv0⟩)).exists
        exact ⟨B, fun _ => hB⟩
    choose t ht using hB
    choose Λ hΛ using fun τ => (p1 τ).exists
    exact ⟨Λ, t, And.intro hΛ ht⟩
  · refine ⟨funext fun τ => (p1 τ).unique (h.1 τ) (h'.1 τ), fun w hw => ?_⟩
    have hs := h.2 w hw
    exact (p2 w hs.2.1).unique hs (h'.2 w hw)
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem exists_esymm_ne {s t : Multiset ℂ} {n : ℕ} (hs : s.card = n) (ht : t.card = n) (h : s ≠ t) :
    ∃ k : Fin n, s.esymm (k + 1) ≠ t.esymm (k + 1) := by
  by_contra hc
  push Not at hc
  apply h
  have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod = (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    have : s.esymm j = t.esymm j := by
      rcases j with _ | j
      · simp [Multiset.esymm]
      · exact hc ⟨j, by omega⟩
    rw [this]
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem one_factor (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (Pl K))
    (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (Λ' : (K →+* ℂ) → Multiset ℂ) (t' : Pl K → Multiset ℂ)
    (h1 : ∀ τ, (Λ τ).card = n) (h2 : ∀ w ∉ S, (t w).card = n) (h3 : ∀ τ, (Λ' τ).card = n)
    (h4 : ∀ w ∉ S, (t' w).card = n) (h : ¬ (Λ = Λ' ∧ ∀ w ∉ S, t w = t' w)) :
    ∃ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ S) ∧ (∀ x : ℝ, x ≠ 0 → val x Λ t P ≠ 0) ∧ ∀ x : ℝ, val x Λ' t' P = 0 := by
  classical
  by_cases hΛ : Λ = Λ'
  · have : ∃ w, w ∉ S ∧ t w ≠ t' w := by
      by_contra hc
      push Not at hc
      exact h ⟨hΛ, hc⟩
    obtain ⟨w, hw, hne⟩ := this
    obtain ⟨k, hk⟩ := exists_esymm_ne (h2 w hw) (h4 w hw) hne
    refine ⟨X (w, k) - C (C ((t' w).esymm (k + 1))), ?_, ?_, ?_⟩
    · intro y hy
      have := vars_sub_subset _ hy
      rw [vars_C, vars_X, Finset.union_empty, Finset.mem_singleton] at this
      rw [this]; exact hw
    · intro x _
      simpa [val, hval, sub_eq_zero] using hk
    · intro x
      simp [val, hval]
  · obtain ⟨τ, hne⟩ := Function.ne_iff.mp hΛ
    obtain ⟨k, hk⟩ := exists_esymm_ne (h1 τ) (h3 τ) hne
    refine ⟨C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none), ?_, ?_, ?_⟩
    · intro y hy
      rw [vars_C] at hy
      exact absurd hy (Finset.notMem_empty _)
    · intro x hx
      have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      have e : val x Λ t (C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none) : PR K n) =
          x * ((Λ τ).esymm (k + 1) - (Λ' τ).esymm (k + 1)) := by
        rw [val, eval₂Hom_C]
        simp
        ring
      rw [e]
      exact mul_ne_zero hx' (sub_ne_zero.mpr hk)
    · intro x
      rw [val, eval₂Hom_C]
      simp
      ring

theorem UpperTheory.ConvolutionTheory.Ci.sepPoly :
    SepPoly := by
  classical
  intro K _ _ n S Λ t I _ Λ' t' h1 h2 h3 h4 h
  choose P hP1 hP2 hP3 using fun i => one_factor K n S Λ t (Λ' i) (t' i) h1 h2 (h3 i) (h4 i) (h i)
  set Q : PR K n := ∏ i, P i with hQ
  refine ⟨Q, Q.vars.image Prod.fst, max Q.totalDegree (Q.support.sup fun β => (Q.coeff β).totalDegree), ?_,
    ⟨?_, le_max_left _ _, ?_⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (vars_prod P hy)
    exact hP1 i y hi
  · intro y hy
    exact Finset.mem_image_of_mem _ hy
  · intro β
    by_cases hβ : β ∈ Q.support
    · exact le_max_of_le_right (Finset.le_sup (f := fun β => (Q.coeff β).totalDegree) hβ)
    · rw [notMem_support_iff.mp hβ, totalDegree_zero]
      exact Nat.zero_le _
  · intro x hx
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hP2 i x hx
  · intro i x
    rw [hQ, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hP3 i x)
end
