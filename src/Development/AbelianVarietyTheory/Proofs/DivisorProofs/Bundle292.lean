module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle178
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem exists_pow_mul_eq_zero_of_represents_away {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop}
    (hbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
      Q R' f → Q R'' (g.comp f))
    (a : A) {Ja : Ideal (Localization.Away a)}
    (hJa : Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) Ja)
    {R' : Type} [CommRing R'] (f : A →+* R') (hf : Q R' f) (x : A)
    (hx : algebraMap A (Localization.Away a) x ∈ Ja) : ∃ m : ℕ, f a ^ m * f x = 0 := by
  have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
      (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
  have h1 : Q _ ((algebraMap R' (Localization.Away (f a))).comp f) :=
    hbc _ _ (algebraMap R' (Localization.Away (f a))) f hf
  rw [← e] at h1
  have h2 := (hJa _ (Localization.awayMap f a)).1 h1 hx
  rw [RingHom.mem_ker, ← RingHom.comp_apply, e, RingHom.comp_apply,
    IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))] at h2
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := h2
  exact ⟨m, hm⟩

theorem represents_of_away_cover : ∀ (A : Type) [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
    Q R' f → Q R'' (g.comp f)) →
  (∀ (R' : Type) [CommRing R'] (f : A →+* R') (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
    (∀ r ∈ t, Q (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) → Q R' f) →
  ∀ (s : Finset A), Ideal.span (s : Set A) = ⊤ →
  (∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
    Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) J) →
  ∃ J : Ideal A, Represents Q J := by
  classical
  intro A _ Q hbc hloc s hs hJ
  choose! J' hJ' using hJ
  refine ⟨⨅ a ∈ s, (J' a).comap (algebraMap A (Localization.Away a)),
    fun R' _ f ↦ ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩⟩
  · intro x hx
    simp only [Submodule.mem_iInf, Ideal.mem_comap] at hx
    rw [RingHom.mem_ker]
    have hspan : Ideal.span ((f : A → R') '' (s : Set A)) = ⊤ := by
      rw [← Ideal.map_span, hs, Ideal.map_top]
    have := Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule R' R') _ hspan (f x) ?_
    · simpa using this
    rintro ⟨_, b, hb, rfl⟩
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc b (hJ' b hb) f hf x (hx b hb)
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  · apply hloc R' f (s.image f)
    · rw [Finset.coe_image, ← Ideal.map_span, hs, Ideal.map_top]
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hr
    have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
        (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
    rw [← e]
    refine ((hJ' a ha) _ (Localization.awayMap f a)).2 ?_
    intro j hj
    obtain ⟨⟨y, _, n, rfl⟩, hy⟩ := IsLocalization.surj (Submonoid.powers a) j
    simp only at hy
    have hyJ : algebraMap A (Localization.Away a) y ∈ J' a := hy ▸ Ideal.mul_mem_right _ _ hj
    have hb : ∀ b ∈ s, ∃ m : ℕ, algebraMap A (Localization.Away b) (a ^ m * y) ∈ J' b := by
      intro b hbs
      let p : A →+* (Localization.Away b ⧸ J' b) :=
        (Ideal.Quotient.mk (J' b)).comp (algebraMap A (Localization.Away b))
      have hp : Q _ p := ((hJ' b hbs) _ (Ideal.Quotient.mk (J' b))).2 (by rw [Ideal.mk_ker])
      obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc a (hJ' a ha) p hp y hyJ
      refine ⟨m, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [p] using hm
    choose! m hm using hb
    have hM : a ^ (s.sup m) * y ∈ ⨅ b ∈ s, (J' b).comap (algebraMap A (Localization.Away b)) := by
      simp only [Submodule.mem_iInf, Ideal.mem_comap]
      intro b hbs
      have : a ^ (s.sup m) * y = a ^ (s.sup m - m b) * (a ^ m b * y) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hbs)]
      rw [this, map_mul]
      exact Ideal.mul_mem_left _ _ (hm b hbs)
    have h0 := hf hM
    rw [RingHom.mem_ker, map_mul, map_pow] at h0
    rw [RingHom.mem_ker]
    have hu : IsUnit (Localization.awayMap f a (algebraMap A _ (a ^ n))) := by
      rw [← RingHom.comp_apply, e, RingHom.comp_apply, map_pow]
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f a)) (f a)).pow n
    have h3 : Localization.awayMap f a j * Localization.awayMap f a (algebraMap A _ (a ^ n)) = 0 := by
      rw [← map_mul, hy, ← RingHom.comp_apply, e, RingHom.comp_apply,
        IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))]
      exact ⟨⟨_, s.sup m, rfl⟩, h0⟩
    exact (hu.mul_left_eq_zero).1 h3

end GlobalTheory.PtClosed
end

section

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceTaylor

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_padL_le {κ κ' : Type} [Fintype κ] [Fintype κ'] (h : κ → V) :
    ‖(padL (κ' := κ') h : κ ⊕ κ' → V)‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simpa [padL] using norm_le_pi_norm h i
  | inr j => simp [padL]

theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] :
    ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

theorem norm_le_norm_elim_add {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) (s : ℝ) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V) + s • padL h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have := norm_le_pi_norm ((Sum.elim x y : κ ⊕ κ' → V) + s • padL h) (Sum.inr j)
  simp only [Pi.add_apply, Pi.smul_apply, padL, Sum.elim_inr, Pi.zero_apply, smul_zero, add_zero] at this
  exact this

theorem norm_iteratedFDeriv_pd_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : X) (g : SchwartzMap X ℂ) (n : ℕ) (w : X) :
    ‖iteratedFDeriv ℝ n (pd a g) w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g w‖ := by
  have e1 : (⇑(pd a g)) = fun y => fderiv ℝ g y a := by funext y; exact pd_apply a g y
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    g.smooth'.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have e : iteratedFDeriv ℝ n (pd a g) w = fderiv ℝ (iteratedFDeriv ℝ n g) w a := by
    ext m
    rw [e1, ← GlobalTheory.SchwartzTranslate.fderiv_iteratedFDeriv_apply_comm a n g g.smooth']
    have := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m).hasFDerivAt.comp
      w (hd w).hasFDerivAt).fderiv
    have e2 : (fun y => iteratedFDeriv ℝ n g y m) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m) ∘ iteratedFDeriv ℝ n g := rfl
    rw [e2, this]
    rfl
  rw [e, ← norm_fderiv_iteratedFDeriv, mul_comm]
  exact (fderiv ℝ (iteratedFDeriv ℝ n g) w).le_opNorm a

theorem elim_add_padL {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) :
    (Sum.elim (x + h) y : κ ⊕ κ' → V) = Sum.elim x y + padL h := by
  funext i
  cases i with
  | inl i => simp [padL]
  | inr j => simp [padL]

theorem seminorm_slice_taylor_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (k n : ℕ) (x h : κ → V) :
    SchwartzMap.seminorm ℂ k n (sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x) ≤
      ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f := by
  set a : κ ⊕ κ' → V := padL (κ' := κ') h with ha
  set f1 := pd a f with hf1
  set f2 := pd a f1 with hf2
  set M := ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f with hM
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun y => ?_
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have c1 : ContDiff ℝ ∞ f1 := f1.smooth'
  have e1 : (fun z => fderiv ℝ f z a) = ⇑f1 := by funext z; exact (pd_apply a f z).symm
  have e2 : (fun z => fderiv ℝ f1 z a) = ⇑f2 := by funext z; exact (pd_apply a f1 z).symm
  set G : (κ ⊕ κ' → V) → ℂ := fun w => f (w + a) - f w - f1 w with hG
  have cG : ContDiff ℝ ∞ G :=
    ((c0.comp (contDiff_id.add contDiff_const)).sub c0).sub c1
  set c : κ ⊕ κ' → V := Sum.elim x 0 with hc
  have efun : ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x)
      = (fun u => G (u + c)) ∘ ⇑(inrL (V := V) κ κ') := by
    funext y'
    have hy : (Sum.elim x y' : κ ⊕ κ' → V) = inrL κ κ' y' + c := by
      rw [add_comm]; exact congrFun (elim_eq_add x) y'
    simp only [SchwartzMap.sub_apply, sliceR_apply, Function.comp_apply, hG, ← hy,
      elim_add_padL, ha]
  have cGc : ContDiff ℝ ∞ (fun u => G (u + c)) := cG.comp (contDiff_id.add contDiff_const)
  have eit : iteratedFDeriv ℝ n ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x) y
      = (iteratedFDeriv ℝ n f (Sum.elim x y + a) - iteratedFDeriv ℝ n f (Sum.elim x y)
          - iteratedFDeriv ℝ n f1 (Sum.elim x y)).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ') := by
    have hy : inrL (V := V) κ κ' y + c = Sum.elim x y := by
      rw [add_comm]; exact (congrFun (elim_eq_add x) y).symm
    rw [efun, ContinuousLinearMap.iteratedFDeriv_comp_right _ cGc _ hnn, iteratedFDeriv_comp_add_right, hy]
    congr 1
    have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
    change iteratedFDeriv ℝ n (((fun z => f (z + a)) - ⇑f) - ⇑f1) _ = _
    rw [iteratedFDeriv_sub_apply (f := (fun z => f (z + a)) - ⇑f) (g := ⇑f1) ((ct.sub c0).of_le hnn).contDiffAt (c1.of_le hnn).contDiffAt,
      iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  rw [eit]
  set z : κ ⊕ κ' → V := Sum.elim x y with hz
  have key := GlobalTheory.SchwartzTranslate.taylor_two (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f1 (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f2 (z + s • a))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f c0 z s
      rw [e1] at this
      exact this.const_smul (‖y‖ ^ k))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f1 c1 z s
      rw [e2] at this
      exact this.const_smul (‖y‖ ^ k))
    M
    (fun s _ => by
      set w := z + s • a
      have hyw : ‖y‖ ≤ ‖w‖ := norm_le_norm_elim_add x h y s
      have b1 := norm_iteratedFDeriv_pd_le a f1 n w
      have b2 := norm_iteratedFDeriv_pd_le a f (n + 1) w
      have hah : ‖a‖ ≤ ‖h‖ := norm_padL_le h
      have hS := SchwartzMap.le_seminorm ℂ k (n + 2) f w
      have hb : ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖ := by
        calc ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) f1 w‖ := b1
          _ ≤ ‖a‖ * (‖a‖ * ‖iteratedFDeriv ℝ (n + 1 + 1) f w‖) := by gcongr
          _ ≤ ‖h‖ * (‖h‖ * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
          _ = _ := by ring
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f2 w‖
          ≤ ‖w‖ ^ k * (‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
        _ = ‖h‖ ^ 2 * (‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by ring
        _ ≤ M := by rw [hM]; gcongr) 1 (by simp)
  simp only [zero_smul, add_zero, one_smul, one_pow, mul_one] at key
  rw [← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  calc ‖y‖ ^ k * ‖(iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ')‖
      ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z‖ := by
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
    _ ≤ M := key

end GlobalTheory.SliceTaylor
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem glue_comma_of_basis : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T s hs
  have key : ∀ (t₁ t₂ : C') (u₁ : T ⟶ G.obj t₁) (u₂ : T ⟶ G.obj t₂) (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ u₁) = mp F w₂ (s t₂ u₂) := by
    intro t₁ t₂ u₁ u₂ S w₁ w₂
    obtain ⟨n, b, hb, hb'⟩ := hdir t₁ t₂ S w₁ w₂
    refine sub_eq_zero.1 (GlobalTheory.CatCoh.Desc.sep_std H hb _ fun S' u' ⟨i, hi⟩ ↦ ?_)
    obtain ⟨t₃, ⟨a₁⟩, ⟨a₂⟩, ⟨g⟩⟩ := hb' i S' u' hi
    have e1 : mp F u' (mp F w₁ (s t₁ u₁)) = mp F g (s t₃ (u₁ ≫ G.map a₁)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₁ ≫ g) (w₁ ≫ u')]
    have e2 : mp F u' (mp F w₂ (s t₂ u₂)) = mp F g (s t₃ (u₂ ≫ G.map a₂)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₂ ≫ g) (w₂ ≫ u')]
    have e3 : u₁ ≫ G.map a₁ = u₂ ≫ G.map a₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov T
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), mp F w (s t v) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t, v, w, -⟩ := hb' i S u hi
      exact ⟨mp F w (s t v), fun _ ↦ ⟨t, v, w, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := GlobalTheory.CatCoh.Desc.glue_std H hb σ fun S S' u ψ hp ↦ by
    obtain ⟨t, v, w, e⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, isUnit_comp ψ hi⟩
    rw [← e, ← e', ← mp_comp]
    exact key _ _ _ _ _ _ _
  refine ⟨x, fun t u ↦ ?_⟩
  have hb2 : Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
    have := congrArg (Ideal.map (mp F u)) hb
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  refine sub_eq_zero.1 (GlobalTheory.CatCoh.Desc.sep_std H hb2 _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e', key t' t v' u S' w' ψ, sub_self]

end GlobalTheory.CatCoh.Desc
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem sep_of_covBy : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Sep (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H _ t Sg _ hcov
  obtain ⟨n, b, hb, hc⟩ := hcov
  intro x hx
  refine Desc.sep_std H hb x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t', a, ha, ⟨w⟩⟩ := hc i S u hi
  have e : u = G.map a ≫ w := Subsingleton.elim _ _
  have h0 : mp F (G.map a) x = 0 := hx t' a ha
  rw [e, mp_comp, h0, map_zero]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.SeqFirst

theorem isIso_restrict_of_le {X Y : Scheme.{0}} (s : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    [IsIso (s ∣_ U)] : IsIso (s ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 : IsIso ((s ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict s U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq s e)).1 h1

theorem exists_preimage {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {y : Y} (hy : y ∈ U) :
    ∃ x ∈ s ⁻¹ᵁ U, s x = y := by
  obtain ⟨z, hz⟩ := (s ∣_ U).homeomorph.surjective ⟨y, hy⟩
  refine ⟨z.1, z.2, ?_⟩
  have := congrArg Subtype.val hz
  rw [← morphismRestrict_base_coe]
  exact this

theorem injOn {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {a b : X}
    (ha : a ∈ s ⁻¹ᵁ U) (hb : b ∈ s ⁻¹ᵁ U) (h : s a = s b) : a = b := by
  obtain ⟨za, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨zb, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = b := ⟨⟨b, hb⟩, rfl⟩
  have : (s ∣_ U) za = (s ∣_ U) zb :=
    Subtype.ext ((morphismRestrict_base_coe s U za).trans (h.trans (morphismRestrict_base_coe s U zb).symm))
  exact congrArg Subtype.val ((s ∣_ U).homeomorph.injective this)

theorem isOpen_image {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {A : Set X}
    (hA : IsOpen A) : IsOpen (s '' (A ∩ s ⁻¹ᵁ U)) := by
  have h1 : IsOpenMap (fun z : (s ⁻¹ᵁ U) => s z.1) := by
    have : (fun z : (s ⁻¹ᵁ U) => s z.1) = (fun w : U => w.1) ∘ (s ∣_ U) := by
      funext z; exact (morphismRestrict_base_coe s U z).symm
    rw [this]
    exact U.isOpenEmbedding'.isOpenMap.comp (s ∣_ U).homeomorph.isOpenMap
  have h2 : s '' (A ∩ s ⁻¹ᵁ U) = (fun z : (s ⁻¹ᵁ U) => s z.1) '' ((fun z : (s ⁻¹ᵁ U) => z.1) ⁻¹' A) := by
    ext y; constructor
    · rintro ⟨x, ⟨hxA, hxU⟩, rfl⟩; exact ⟨⟨x, hxU⟩, hxA, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z.1, ⟨hz, z.2⟩, rfl⟩
  rw [h2]
  exact h1 _ (hA.preimage continuous_subtype_val)

end GlobalTheory.SeqFirst


open GlobalTheory.SeqFirst in
theorem GlobalTheory.isIso_near_or_centre_meets : ∀ {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) (y : Y) {Y' : Scheme.{0}} (s : Y' ⟶ Y), GlobalTheory.IsSmoothBlowupSeq f B s → (∃ U : Y.Opens, y ∈ U ∧ IsIso (s ∣_ U)) ∨ ∃ (Y₁ : Scheme.{0}) (s₁ : Y₁ ⟶ Y) (J : Y₁.IdealSheafData) (U : Y.Opens) (y₁ : Y₁), GlobalTheory.IsSmoothBlowupSeq f B s₁ ∧ Smooth (J.subschemeι ≫ s₁ ≫ f) ∧ (J.support : Set Y₁) ⊆ s₁ ⁻¹' B ∧ y ∈ U ∧ IsIso (s₁ ∣_ U) ∧ y₁ ∈ J.support ∧ s₁ y₁ = y := by
  intro S Y f B y Y' s h
  induction h with
  | id => exact Or.inl ⟨⊤, trivial, inferInstance⟩
  | @step Y₁ Y₂ s J π hs h₁ h₂ h₃ ih =>
    rcases ih with ⟨U, hyU, hU⟩ | hr
    · obtain ⟨y', hy'U, hy'⟩ := exists_preimage s hyU
      by_cases hJ : y' ∈ J.support
      · exact Or.inr ⟨Y₁, s, J, U, y', hs, h₁, h₂, hyU, hU, hJ, hy'⟩
      · left
        have hA : IsOpen ((J.support : Set Y₁)ᶜ) := J.support.isClosed.isOpen_compl
        let V : Y.Opens := ⟨s '' ((J.support : Set Y₁)ᶜ ∩ s ⁻¹ᵁ U), isOpen_image s hA⟩
        have hVU : V ≤ U := by
          rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
        have hyV : y ∈ V := ⟨y', ⟨hJ, hy'U⟩, hy'⟩
        refine ⟨V, hyV, ?_⟩
        have : IsIso (s ∣_ V) := isIso_restrict_of_le s hVU
        have hπ : IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
          refine Principalise.isIso_restrict_of_blowup h₃ _ ?_
          intro x hx hxJ
          have hxU : x ∈ s ⁻¹ᵁ U := hVU hx
          obtain ⟨w, ⟨hwA, hwU⟩, hw⟩ := (hx : s x ∈ V)
          exact hwA (injOn s hwU hxU hw ▸ hxJ)
        rw [morphismRestrict_comp]
        exact IsIso.comp_isIso' hπ this
    · right; exact hr
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schrodinger_rep_unitary : ∀ (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ),
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  first | exact @GlobalTheory.RealWeil.integral_rhoFun_mul_conj | exact GlobalTheory.RealWeil.integral_rhoFun_mul_conj | (intros; apply GlobalTheory.RealWeil.integral_rhoFun_mul_conj <;> assumption)
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm → (∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) → ∀ x : EuclideanSpace ℝ l, f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by
  first | exact @GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec | exact GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec | (intros; apply GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec <;> assumption)
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.continuous_matrix_coefficient : ∀ (n : ℕ) (g g' : Sch (Fin n)), Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  first | exact @GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | exact GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | (intros; apply GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun <;> assumption)
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.matrix_coeff_decay_first_part : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖pPart w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.matrixCoeff_pPart_decay | exact GlobalTheory.matrixCoeff_pPart_decay | (intros; apply GlobalTheory.matrixCoeff_pPart_decay <;> assumption)
end

section

open scoped SchwartzMap Matrix

theorem _root_.GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  first | exact @GlobalTheory.exists_symplecticGroup_of_sympl | exact GlobalTheory.exists_symplecticGroup_of_sympl | (intros; apply GlobalTheory.exists_symplecticGroup_of_sympl <;> assumption)
end
