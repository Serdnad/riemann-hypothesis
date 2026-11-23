module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

@[expose] public section

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.CosetEval

def mfMonoid (Γ : Subgroup SL(2, ℤ)) : Submonoid (Multiplicative ℤ × (ℍ → ℂ)) where
  carrier := {p | IsMF Γ (Multiplicative.toAdd p.1) p.2}
  mul_mem' := by
    rintro ⟨a, f⟩ ⟨b, g⟩ ha hb
    exact IsMF.mul ha hb (by simp)
  one_mem' := IsMF.one Γ

def evHom (Γ : Subgroup SL(2, ℤ)) (x : SL(2, ℤ)) (τ : ℍ) : mfMonoid Γ →* ℂ where
  toFun p := (p.1.2 ∣[Multiplicative.toAdd p.1.1] x) τ
  map_one' := by
    show ((1 : ℍ → ℂ) ∣[Multiplicative.toAdd (1 : Multiplicative ℤ)] x) τ = 1
    rw [toAdd_one, ModularForm.is_invariant_one]; rfl
  map_mul' p q := by
    show ((p.1.2 * q.1.2) ∣[Multiplicative.toAdd (p.1.1 * q.1.1)] x) τ = _
    rw [toAdd_mul, ModularForm.mul_slash_SL2]; rfl

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
private lemma dense_setOf_ne_zero_of_mdifferentiable_of_ne_zero {D : ℍ → ℂ} (hD : MDiff D) (hD0 : D ≠ 0) :
    Dense {τ | D τ ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨τ, hτ⟩
  by_contra hempty
  have hzero : ∀ σ ∈ U, D σ = 0 := fun σ hσ => by_contra fun h => hempty ⟨σ, hσ, h⟩
  have hS : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ (D ∘ ofComplex) {w : ℂ | 0 < w.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hD).analyticOnNhd hS
  have hev : D ∘ ofComplex =ᶠ[𝓝 (τ : ℂ)] 0 := by
    have hUc : IsOpen (((↑) : ℍ → ℂ) '' U) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
    filter_upwards [hUc.mem_nhds ⟨τ, hτ, rfl⟩] with w hw
    obtain ⟨σ, hσ, rfl⟩ := hw
    simp [hzero σ hσ]
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ.im_pos hev
  apply hD0
  funext σ
  simpa using hall σ.im_pos


open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
theorem _root_.GlobalTheory.CosetEval.evals_independent : ∀ M : ℕ, 0 < M → (∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f) → ∃ τ₀ : ℍ, ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0 := by
  intro M _ hsep
  classical
  have hsep' : ∀ p : SL(2, ℤ) × SL(2, ℤ), ∃ (k : ℤ) (f : ℍ → ℂ),
      _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f ∧
      (p.1 * p.2⁻¹ ∉ CongruenceSubgroup.Gamma M → f ∣[k] p.1 ≠ f ∣[k] p.2) := by
    intro p
    by_cases hp : p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M
    · exact ⟨0, 0, _root_.GlobalTheory.OddFrame.IsMF.zero _ _, fun h => absurd hp h⟩
    · obtain ⟨k, f, hf, hne⟩ := hsep _ hp
      refine ⟨k, f, hf, fun _ heq => hne ?_⟩
      have := congrArg (fun g => g ∣[k] p.2⁻¹) heq

      rwa [← SlashAction.slash_mul, ← SlashAction.slash_mul, mul_inv_cancel,
        SlashAction.slash_one] at this
  choose k f hf hne using hsep'
  set O : SL(2, ℤ) × SL(2, ℤ) → Set ℍ := fun p =>
    {_τ | p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M} ∪
      {τ | (f p ∣[k p] p.1) τ ≠ (f p ∣[k p] p.2) τ} with hO
  have hcont : ∀ p (y : SL(2, ℤ)), Continuous (f p ∣[k p] y) := fun p y =>
    (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ y).continuous
  have hOopen : ∀ p, IsOpen (O p) := fun p =>
    isOpen_const.union (isOpen_ne_fun (hcont p p.1) (hcont p p.2))
  have hOdense : ∀ p, Dense (O p) := by
    intro p
    by_cases hp : p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M
    · exact dense_univ.mono fun τ _ => Or.inl hp
    · have hD : MDiff (f p ∣[k p] p.1 - f p ∣[k p] p.2) :=
        (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ _).sub (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ _)
      refine (dense_setOf_ne_zero_of_mdifferentiable_of_ne_zero hD
        (fun h0 => hne p hp (sub_eq_zero.1 h0))).mono fun τ hτ => Or.inr ?_
      exact sub_ne_zero.1 hτ
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := Subtype.countable
  obtain ⟨τ₀, hτ₀⟩ := (dense_iInter_of_isOpen hOopen hOdense).nonempty
  refine ⟨τ₀, fun ι _ x c hx hc => ?_⟩
  let χ : ι → (_root_.GlobalTheory.CosetEval.mfMonoid (CongruenceSubgroup.Gamma M) →* ℂ) :=
    fun i => _root_.GlobalTheory.CosetEval.evHom (CongruenceSubgroup.Gamma M) (x i) τ₀
  have hinj : Function.Injective χ := by
    intro i j hij
    by_contra hij'
    have hnot : x i * (x j)⁻¹ ∉ CongruenceSubgroup.Gamma M := fun h => hij' (hx i j h)
    rcases Set.mem_iInter.1 hτ₀ (x i, x j) with h | h
    · exact hnot h
    · exact h (DFunLike.congr_fun hij
        ⟨(Multiplicative.ofAdd (k (x i, x j)), f (x i, x j)), hf (x i, x j)⟩)
  have hli := (linearIndependent_monoidHom (_root_.GlobalTheory.CosetEval.mfMonoid (CongruenceSubgroup.Gamma M)) ℂ).comp χ hinj
  funext i
  refine Fintype.linearIndependent_iff.1 hli c ?_ i
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
  exact hc _ _ p.2

end GlobalTheory.CosetEval
end
end

section

noncomputable section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem exists_coset_reps {M : ℕ} (hM : 0 < M) (Γ : Subgroup SL(2, ℤ)) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Nonempty Q) (t : Q → SL(2, ℤ)), (∀ q, t q ∈ Γ) ∧
      (∀ q q', t q * (t q')⁻¹ ∈ CongruenceSubgroup.Gamma M → q = q') ∧
      ∀ γ ∈ Γ, ∃ π : Equiv.Perm Q, ∀ q, ∃ g ∈ CongruenceSubgroup.Gamma M, t q * γ = g * t (π q) := by
  classical
  have : (CongruenceSubgroup.Gamma M).FiniteIndex := finiteIndex_of_Gamma_le hM le_rfl
  have : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M

  let H : Subgroup (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M) :=
    Γ.map (QuotientGroup.mk' (CongruenceSubgroup.Gamma M))
  have hq : ∀ q : H, ∃ γ ∈ Γ, QuotientGroup.mk' (CongruenceSubgroup.Gamma M) γ = (q : _) :=
    fun q => Subgroup.mem_map.1 q.2
  choose t ht hmk using hq
  refine ⟨H, Fintype.ofFinite H, ⟨1⟩, t, ht, ?_, ?_⟩
  · intro q q' h
    apply Subtype.ext
    rw [← hmk q, ← hmk q', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact h
  · intro γ hγ
    let g : H := ⟨QuotientGroup.mk' _ γ, Subgroup.mem_map_of_mem _ hγ⟩
    refine ⟨Equiv.mulRight g, fun q => ⟨t q * γ * (t (Equiv.mulRight g q))⁻¹, ?_, by group⟩⟩
    have h1 : QuotientGroup.mk' (CongruenceSubgroup.Gamma M) (t q * γ) =
        QuotientGroup.mk' (CongruenceSubgroup.Gamma M) (t (Equiv.mulRight g q)) := by
      rw [map_mul, hmk, hmk]
      rfl
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv] at h1
    exact h1

theorem IsMF.sum_slash_reps {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {Q : Type} [Fintype Q] {t : Q → SL(2, ℤ)}
    (ht : ∀ γ ∈ Γ, ∃ π : Equiv.Perm Q, ∀ q, ∃ g ∈ CongruenceSubgroup.Gamma M, t q * γ = g * t (π q))
    {k : ℤ} {f : ℍ → ℂ} (hf : IsMF (CongruenceSubgroup.Gamma M) k f) : IsMF Γ k (∑ q, f ∣[k] t q) := by
  classical
  have : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M
  have hsum : ∀ (A : SL(2, ℤ)) (u : Finset Q) (g : Q → ℍ → ℂ),
      (∑ q ∈ u, g q) ∣[k] A = ∑ q ∈ u, g q ∣[k] A := by
    intro A u g
    refine Finset.induction_on u (by simp) ?_
    intro a u ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

  have hx : ∀ x : SL(2, ℤ), IsMF (CongruenceSubgroup.Gamma M) k (f ∣[k] x) := by
    intro x
    unfold IsMF
    refine ⟨fun g hg => ?_, mdiff_slash hf.2.1 k x, fun y => ?_⟩
    · rw [← SlashAction.slash_mul]
      have e : x * g = (x * g * x⁻¹) * x := by group
      rw [e, IsMF.slash_mul hf ((inferInstance : (CongruenceSubgroup.Gamma M).Normal).conj_mem g hg x) x]
    · rw [← SlashAction.slash_mul]
      exact hf.2.2 (x * y)
  have hS : IsMF (CongruenceSubgroup.Gamma M) k (∑ q, f ∣[k] t q) :=
    IsMF.sum Finset.univ (fun q _ => hx (t q))
  unfold IsMF
  refine ⟨fun γ hγ => ?_, hS.2.1, hS.2.2⟩
  obtain ⟨π, hπ⟩ := ht γ hγ
  rw [hsum]
  calc ∑ q, (f ∣[k] t q) ∣[k] γ = ∑ q, f ∣[k] t (π q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        obtain ⟨g, hg, he⟩ := hπ q
        rw [← SlashAction.slash_mul, he, IsMF.slash_mul hf hg]
    _ = ∑ q, f ∣[k] t q := Equiv.sum_comp π (fun q => f ∣[k] t q)

theorem IsReps.signed_reps_injective {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)}
    (hle : CongruenceSubgroup.Gamma M ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    {Q : Type} {t : Q → SL(2, ℤ)} (ht : ∀ q, t q ∈ Γ)
    (hinj : ∀ q q', t q * (t q')⁻¹ ∈ CongruenceSubgroup.Gamma M → q = q') :
    (∀ i j q q', t q * s i * (t q' * s j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j ∧ q = q') ∧
      ∀ i j q q', -(t q * s i * (t q' * s j)⁻¹) ∉ CongruenceSubgroup.Gamma M := by
  have hA : ∀ i j q q' (γ : SL(2, ℤ)), γ ∈ Γ →
      (s i = (t q)⁻¹ * γ * t q' * s j ∨ s i = -((t q)⁻¹ * γ * t q' * s j)) → i = j := by
    intro i j q q' γ hγ h
    exact hs.2 i j _ (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (ht q)) hγ) (ht q')) h
  have key : ∀ i j q q', (t q)⁻¹ * (t q * s i * (t q' * s j)⁻¹) * t q' * s j = s i := by
    intro i j q q'; group
  have diag : ∀ i q q', t q * s i * (t q' * s i)⁻¹ = t q * (t q')⁻¹ := by
    intro i q q'; group
  refine ⟨fun i j q q' h => ?_, fun i j q q' h => ?_⟩
  · have hij : i = j := hA i j q q' _ (hle h) (Or.inl (key i j q q').symm)
    subst hij
    refine ⟨rfl, hinj q q' ?_⟩
    rwa [diag] at h
  · have hΓ := hle h
    have hij : i = j := by
      refine hA i j q q' _ hΓ (Or.inr ?_)
      rw [mul_neg, neg_mul, neg_mul, key, neg_neg]
    subst hij
    rw [diag] at hΓ
    apply hneg
    have hY : t q * (t q')⁻¹ ∈ Γ := Γ.mul_mem (ht q) (Γ.inv_mem (ht q'))
    have e : (-1 : SL(2, ℤ)) = -(t q * (t q')⁻¹) * (t q * (t q')⁻¹)⁻¹ := by
      rw [neg_mul, mul_inv_cancel]
    rw [e]
    exact Γ.mul_mem hΓ (Γ.inv_mem hY)

theorem exists_odd_det_evM_ne_zero (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (τ₀ : ℍ)
    (hM : 0 < M) (hle : CongruenceSubgroup.Gamma M ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (H : ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ),
      (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) →
      (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) →
      c = 0) :
    ∃ (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧
      (evM s w F τ₀).det ≠ 0 := by
  classical
  obtain ⟨Q, _, ⟨q0⟩, t, ht, hinj, hperm⟩ := exists_coset_reps hM Γ
  have hsum : ∀ (A : SL(2, ℤ)) (k : ℤ) (u : Finset Q) (g : Q → ℍ → ℂ),
      (∑ q ∈ u, g q) ∣[k] A = ∑ q ∈ u, g q ∣[k] A := by
    intro A k u g
    refine Finset.induction_on u (by simp) ?_
    intro a u ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  obtain ⟨hpos, hneg'⟩ := IsReps.signed_reps_injective hle hneg hs ht hinj

  let vec : ℤ → (ℍ → ℂ) → Fin r → ℂ := fun k f i => ((∑ q, f ∣[k] t q) ∣[k] s i) τ₀
  let V : Set (Fin r → ℂ) :=
    {v | ∃ k f, Odd k ∧ IsMF (CongruenceSubgroup.Gamma M) k f ∧ v = vec k f}
  have hvec : ∀ k f i, vec k f i = ∑ q, (f ∣[k] (t q * s i)) τ₀ := by
    intro k f i
    simp only [vec]
    rw [hsum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun q _ => by rw [SlashAction.slash_mul]

  have hV : Submodule.span ℂ V = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : Fin r → ℂ := fun i => φ (fun j => if i = j then 1 else 0)
    have hφc : ∀ v, φ v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ φ v]
      simp only [c, smul_eq_mul]
    apply hφ
    have hc0 : c = 0 := by
      let x : Bool × Fin r × Q → SL(2, ℤ) := fun a =>
        if a.1 then t a.2.2 * s a.2.1 else -(t a.2.2 * s a.2.1)
      let c' : Bool × Fin r × Q → ℂ := fun a => if a.1 then c a.2.1 else -c a.2.1
      have ineg : ∀ B : SL(2, ℤ), (-B)⁻¹ = -B⁻¹ := fun B =>
        inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
      have hx : ∀ a b, x a * (x b)⁻¹ ∈ CongruenceSubgroup.Gamma M → a = b := by
        rintro ⟨_ | _, i, q⟩ ⟨_ | _, j, q'⟩ h <;>
          simp only [x, Bool.false_eq_true, ↓reduceIte] at h
        · rw [ineg, neg_mul_neg] at h
          obtain ⟨rfl, rfl⟩ := hpos i j q q' h
          rfl
        · rw [neg_mul] at h
          exact absurd h (hneg' i j q q')
        · rw [ineg, mul_neg] at h
          exact absurd h (hneg' i j q q')
        · obtain ⟨rfl, rfl⟩ := hpos i j q q' h
          rfl
      have hrel : ∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f →
          ∑ a, c' a * (f ∣[k] x a) τ₀ = 0 := by
        intro k f hf
        rw [Fintype.sum_prod_type, Fintype.sum_bool]
        simp only [x, c', Bool.false_eq_true, ↓reduceIte]
        rcases Int.even_or_odd k with hk | hk
        · simp only [slash_neg_of_even hk, neg_mul, Finset.sum_neg_distrib, add_neg_cancel]
        · have h0 : φ (vec k f) = 0 := hker (Submodule.subset_span ⟨k, f, hk, hf, rfl⟩)
          rw [hφc] at h0
          simp only [hvec] at h0
          have hS : ∑ i, ∑ q, c i * (f ∣[k] (t q * s i)) τ₀ = 0 := by
            rw [← h0]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum, mul_comm]
          simp only [slash_neg_of_odd hk, Pi.neg_apply, neg_mul_neg]
          rw [Fintype.sum_prod_type, hS, add_zero]
      have hc'0 := H _ x c' hx hrel
      funext i
      simpa [c'] using congrFun hc'0 (true, i, q0)
    refine LinearMap.ext fun v => ?_
    rw [hφc v, hc0]
    simp

  obtain ⟨b, hbV, hspan, hli⟩ := exists_linearIndependent ℂ V
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hspan, hV]
  let e := (Pi.basisFun ℂ (Fin r)).indexEquiv (Module.Basis.mk hli hsp)
  have hmem : ∀ j, ∃ k f, Odd k ∧ IsMF (CongruenceSubgroup.Gamma M) k f ∧
      (e j : Fin r → ℂ) = vec k f := fun j => hbV (e j).2
  choose w f hw hf hv using hmem
  refine ⟨w, fun j => ∑ q, f j ∣[w j] t q, fun j => ⟨hw j, IsMF.sum_slash_reps hperm (hf j)⟩, ?_⟩
  have hcols : (fun j => Matrix.transpose (evM s w (fun j => ∑ q, f j ∣[w j] t q) τ₀) j) =
      fun j => (e j : Fin r → ℂ) := by
    funext j i
    rw [hv j]
    rfl
  have hli' : LinearIndependent ℂ (fun j => Matrix.transpose (evM s w (fun j => ∑ q, f j ∣[w j] t q) τ₀) j) := by
    rw [hcols]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli')).ne_zero

end GlobalTheory.OddFrame
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame.ThirdDiv

def uEl : SL(2, ℤ) := ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

noncomputable def μ : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

theorem μ_sq : μ ^ 2 = μ - 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [μ, pow_two] <;> nlinarith [h3]

theorem coe_ρ : (ρ : ℂ) = μ - 1 := by
  apply Complex.ext <;> simp [μ, UpperHalfPlane.ρ] <;> norm_num

theorem μ_ne : μ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [μ] at this

theorem denom_uEl : denom (uEl : GL (Fin 2) ℝ) ρ = μ := by
  simp only [denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  simp [uEl, coe_ρ]

theorem uEl_smul_ρ : uEl • ρ = ρ := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp [uEl, coe_ρ]
  rw [div_eq_iff (by simpa using μ_ne), neg_eq_iff_eq_neg]
  linear_combination μ_sq

theorem re_μ_zpow {w : ℤ} (hw : Odd w) :
    (μ ^ (-w)).re = if (3 : ℤ) ∣ w then -1 else 1 / 2 := by
  have h3 : μ ^ 3 = -1 := by linear_combination (μ + 1) * μ_sq
  have h5 : μ ^ 5 = 1 - μ := by linear_combination μ ^ 2 * h3 - μ_sq
  have h6 : μ ^ (6 : ℤ) = 1 := by
    rw [zpow_ofNat]; linear_combination (μ ^ 3 - 1) * h3
  have key : ∀ q t : ℤ, μ ^ (6 * q + t) = μ ^ t := fun q t => by
    rw [zpow_add₀ μ_ne, zpow_mul, h6, one_zpow, one_mul]
  have hre : μ.re = 1 / 2 := rfl
  obtain ⟨m, hm⟩ := hw
  have hc : -w = 6 * (-w / 6) + 1 ∨ -w = 6 * (-w / 6) + 3 ∨ -w = 6 * (-w / 6) + 5 := by omega
  rcases hc with h | h | h
  · rw [if_neg (by omega), h, key, zpow_one, hre]
  · rw [if_pos (by omega), h, key, zpow_ofNat, h3]; simp
  · rw [if_neg (by omega), h, key, zpow_ofNat, h5, Complex.sub_re, hre]; norm_num

theorem not_fixed {N : ℕ} (hN : 5 ≤ N) {γ x : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) :
    ¬ (x * uEl = γ * x ∨ x * uEl = -(γ * x)) := by
  obtain ⟨h0, h1, -⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have htr : ((x * uEl * x⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_left]
    simp [uEl, Matrix.trace_fin_two]
  rintro (h | h)
  · rw [h, mul_inv_cancel_right, Matrix.trace_fin_two] at htr
    have h2 := congrArg (Int.cast : ℤ → ZMod N) htr
    push_cast at h2
    have h3 : ((1 : ℕ) : ZMod N) = 0 := by
      push_cast; linear_combination h2 - h0 - h1
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega
  · rw [h, neg_mul, mul_inv_cancel_right, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
      Matrix.trace_fin_two] at htr
    have h2 := congrArg (Int.cast : ℤ → ZMod N) htr
    push_cast at h2
    have h3 : ((3 : ℕ) : ZMod N) = 0 := by
      push_cast; linear_combination - h2 - h0 - h1
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega

theorem three_mul_card_dvd (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hN : 5 ≤ N) (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hdet : (evM s w F ρ).det ≠ 0) :
    3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  classical
  obtain ⟨π, hπ⟩ := hs.exists_perm uEl
  have hε : ∀ i, ∃ ε : ℂ, ∀ j, evM s w F ρ i j * μ ^ (-w j) = ε * evM s w F ρ (π i) j := by
    intro i
    have h0 : ∀ j, (F j ∣[w j] (s i * uEl)) ρ = evM s w F ρ i j * μ ^ (-w j) := fun j => by
      rw [slash_mul_apply, uEl_smul_ρ, denom_uEl]; rfl
    obtain ⟨γ, hγ, h | h⟩ := hπ i
    · refine ⟨1, fun j => ?_⟩
      rw [← h0, h, (hF j).2.slash_mul hγ, one_mul]; rfl
    · refine ⟨-1, fun j => ?_⟩
      rw [← h0, h, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul hγ, neg_one_mul]; rfl
  choose ε hε using hε
  have hne : ∀ i, π i ≠ i := fun i hi => by
    obtain ⟨γ, hγ, h⟩ := hπ i
    rw [hi] at h
    exact not_fixed hN (hΓ hγ) h
  set A := evM s w F ρ with hA
  let P : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i i' => if i' = π i then ε i else 0
  have hAP : A * Matrix.diagonal (fun j => μ ^ (-w j)) = P * A := by
    ext i j
    rw [Matrix.mul_diagonal, hε, Matrix.mul_apply]
    simp [P]
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hD : Matrix.diagonal (fun j => μ ^ (-w j)) = A⁻¹ * (P * A) := by
    rw [← hAP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have htr : ∑ j, μ ^ (-w j) = 0 := by
    rw [← Matrix.trace_diagonal, hD, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.mul_one]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [P, (hne i).symm]
  have hre := congrArg Complex.re htr
  rw [Complex.re_sum, Finset.sum_congr rfl fun j _ => re_μ_zpow (hF j).1, Finset.sum_ite] at hre
  simp only [Finset.sum_const, nsmul_eq_mul, Complex.zero_re] at hre
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
    (fun j => (3 : ℤ) ∣ w j)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have hc' := congrArg (Nat.cast : ℕ → ℝ) hc
  push_cast at hc'
  have : (3 : ℝ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℝ) = r := by linarith
  exact_mod_cast this

end GlobalTheory.OddFrame.ThirdDiv
end
