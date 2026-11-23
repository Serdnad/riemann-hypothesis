module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle003
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle009

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.GaugeDeriv

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def linForm {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) :
    MvPowerSeries (ι ⊕ ι') C :=
  (∑ c : ι, e c w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
    ∑ b : ι', e' b w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)

variable {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem hPullW_eq (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW H e e' = MvPowerSeries.subst (linForm e e') H := rfl

theorem constantCoeff_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) :
    MvPowerSeries.constantCoeff (linForm e e' w) = 0 := by
  simp [linForm]

theorem hasSubst_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) :
    MvPowerSeries.HasSubst (linForm e e') := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_linForm e e' w)

theorem pderiv_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (linForm e e' w) = MvPowerSeries.C (e' b w) := by
  classical
  simp [linForm, MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]

theorem dVar_eq {σ : Type} (w : σ) (F : MvPowerSeries σ C) :
    dVar w F = MvPowerSeries.pderiv (R := C) w F := by
  ext μ
  rw [MvPowerSeries.coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem sum_toW {M : Type} [AddCommGroup M] [Module C M] (g : Fin 2) (u : I g → C) (F : WV I → M) :
    ∑ w, toW g u w • F w = ∑ k, u k • F ⟨g, k⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single g]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [toW]
  · intro g' _ hg'
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp [toW, hg']
  · simp

theorem pderiv_hPullW (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (g : Fin 2)
    (v' : ι' → I g → C) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (hPullW H e (fun b => toW g (v' b))) =
      ∑ k, v' b k • hPullW (dVar ⟨g, k⟩ H) e (fun b => toW g (v' b)) := by
  have hs := hasSubst_linForm e (fun b => toW g (v' b))
  rw [hPullW_eq, GlobalTheory.FormalCalc.pderiv_subst hs]
  have key : ∀ w : WV I,
      MvPowerSeries.subst (linForm e (fun b => toW g (v' b))) (MvPowerSeries.pderiv (R := C) w H) *
          MvPowerSeries.pderiv (R := C) (Sum.inr b) (linForm e (fun b => toW g (v' b)) w) =
        toW g (v' b) w • hPullW (dVar w H) e (fun b => toW g (v' b)) := by
    intro w
    rw [pderiv_linForm, hPullW_eq, dVar_eq, MvPowerSeries.smul_eq_C_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  exact sum_toW g (v' b) (fun w => hPullW (dVar w H) e (fun b => toW g (v' b)))

theorem constantCoeff_upG (g : Fin 2) {F : MvPowerSeries (I g) C}
    (hF : MvPowerSeries.constantCoeff F = 0) : MvPowerSeries.constantCoeff (upG g F) = 0 := by
  unfold upG
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _))
    (fun _ => MvPowerSeries.constantCoeff_X _), hF, map_zero]

variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

theorem hPullW_toLeaf (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (a a' : ZMod d)
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b k, (G (1 - g)).ty (Sum.inl k) ≠ a' → v' b k = 0) (F : MvPowerSeries (WV I) C) :
    hPullW (toLeaf G g a a' F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
      hPullW F (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  rw [hPullW_eq, hPullW_eq]
  apply GlobalTheory.subst_eq_of_coeff_eq_of_killed C (WV I) (ι ⊕ ι') (OnLeafV G g a a')
  · exact constantCoeff_linForm _ _
  · rintro ⟨w1, w2⟩ hw
    have h1 : ∀ c, toW g (e c) ⟨w1, w2⟩ = 0 := by
      intro c
      by_cases h : w1 = g
      · subst h
        simp only [toW]
        exact he c w2 (fun hty => hw (Or.inl ⟨rfl, hty⟩))
      · simp [toW, h]
    have h2 : ∀ b, toW (1 - g) (v' b) ⟨w1, w2⟩ = 0 := by
      intro b
      by_cases h : w1 = 1 - g
      · subst h
        simp only [toW]
        exact hv b w2 (fun hty => hw (Or.inr ⟨rfl, hty⟩))
      · simp [toW, h]
    simp [linForm, h1, h2]
  · intro μ hμ
    rw [show MvPowerSeries.coeff μ (toLeaf G g a a' F) = toLeaf G g a a' F μ from rfl]
    unfold toLeaf
    exact if_pos hμ

theorem odd_val_sub {d : ℕ} [NeZero d] (a : ZMod d) {i : ℕ} (hi : Odd i) (hid : i < d) :
    Odd (a + (i : ZMod d) - a).val := by
  rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hid]
  exact hi

private theorem hPullW_add (H H' : MvPowerSeries (WV I) C) (e : ι → WV I → C)
    (e' : ι' → WV I → C) :
    hPullW (H + H') e e' = hPullW H e e' + hPullW H' e e' := by
  rw [hPullW_eq, hPullW_eq, hPullW_eq, MvPowerSeries.subst_add (hasSubst_linForm e e')]

private theorem hPullW_sum_smul {κ : Type} [Fintype κ] (c : κ → C) (F : κ → MvPowerSeries (WV I) C)
    (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW (∑ q, c q • F q) e e' = ∑ q, c q • hPullW (F q) e e' := by
  simp only [hPullW_eq]
  rw [GlobalTheory.FormalCalc.subst_sum' (hasSubst_linForm e e')]
  simp only [MvPowerSeries.subst_smul (hasSubst_linForm e e')]

theorem pderiv_hM : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → ∀ b : ι', ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧ MvPowerSeries.pderiv (R := C) (Sum.inr b) (X.hM g a i e v') = MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • hPullW (upG g ((S g).ze (t g) κ)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  intro C _ V d _ I J _ _ X hAlt g a i hi hid S t ht ι ι' _ _ e v' he hvint hv b
  have hΦ : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_upG w.1 ((ht w.1).1 w.2))
  have hLs := hasSubst_linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))
  have hK : ∀ k : I (1 - g), ∃ γ : MvPowerSeries (WV I) C,
      (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧
      v' b k • hPullW (dVar (⟨1 - g, k⟩ : WV I) (X.hL g a (a + (i : ZMod d))))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
        v' b k • hPullW (∑ κ : J g, X.pair g κ k • upG g ((S g).ze (t g) κ))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) +
        v' b k • hPullW (MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) γ)
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
    intro k
    by_cases hk : (X.G (1 - g)).ty (Sum.inl k) = a + (i : ZMod d)
    · obtain ⟨K, ⟨γ, hγ, rfl⟩, hEq⟩ :=
        X.C_eq hAlt g a (a + (i : ZMod d)) (odd_val_sub a hi hid) S t ht k hk
      refine ⟨γ, hγ, ?_⟩
      rw [sub_eq_iff_eq_add'] at hEq
      rw [hEq, hPullW_add, hPullW_toLeaf X.G g a _ e v' he hv,
        hPullW_toLeaf X.G g a _ e v' he hv, smul_add]
    · refine ⟨0, fun μ => ?_, ?_⟩
      · rw [map_zero]
        exact VF.Ge.zero 0
      · rw [hv b k hk]
        simp only [zero_smul, add_zero]
  choose γ hγint hγeq using hK
  refine ⟨∑ k, v' b k • γ k, ?_, ?_⟩
  · intro μ

    rw [map_sum]
    refine VF.Ge.sum (fun k _ => ?_)
    simp only [map_smul, smul_eq_mul]
    exact VF.Ge.mul_int (hvint b k) (hγint k μ)
  · unfold RowData.hM
    rw [pderiv_hPullW (X.hL g a (a + (i : ZMod d))) (fun c => toW g (e c)) (1 - g) v' b,
      Finset.sum_congr rfl (fun k _ => hγeq k), Finset.sum_add_distrib]
    refine (add_comm _ _).trans ?_
    congr 1
    · simp only [hPullW_eq]
      have hΨ : MvPowerSeries.HasSubst (fun w : WV I =>
          MvPowerSeries.subst (linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)))
            (upG w.1 (t w.1 w.2))) := by
        have h := hΦ.comp hLs
        simp only [MvPowerSeries.substAlgHom_apply] at h
        exact h
      rw [GlobalTheory.FormalCalc.subst_sum' hΨ]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [MvPowerSeries.subst_smul hΨ, MvPowerSeries.subst_comp_subst_apply hΦ hLs]
    · simp only [hPullW_sum_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun κ _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [mul_comm]

end GlobalTheory.GaugeDeriv
end
end

section

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory

theorem ringOfIntegers_hom_injective (E : Type) [Field E] [NumberField E] (C : Type) [Field C]
    [CharZero C] (f : 𝓞 E →+* C) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  simp only [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  simpa using hn

theorem ringOfIntegers_hom_eq_of_congr_maximalIdeal :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ ((p : ℤ) ∣ NumberField.discr E) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsLocalRing O] [Algebra O C], v.Integers O → ¬ IsUnit (p : O) → ∀ σ σ' : 𝓞 E →+* O, (∀ x, σ x - σ' x ∈ maximalIdeal O) → σ = σ' := by
  intro E _ _ p hp hd C _ _ _ v O _ _ _ hv hpu σ σ' hcong
  classical
  by_contra hne
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj

  have hext : ∀ s : 𝓞 E →+* O, ∃ τ : E →ₐ[ℚ] C,
      ∀ x : 𝓞 E, τ (algebraMap (𝓞 E) E x) = algebraMap O C (s x) := by
    intro s
    refine ⟨(IsFractionRing.lift (K := E)
      (ringOfIntegers_hom_injective E C ((algebraMap O C).comp s))).toRatAlgHom, fun x => ?_⟩
    simp
  obtain ⟨τ, hτ⟩ := hext σ
  obtain ⟨τ', hτ'⟩ := hext σ'
  have hττ : τ ≠ τ' := by
    intro h
    apply hne
    ext x
    apply hinj
    rw [← hτ, ← hτ', h]
  have hmem : ∀ (φ : E →ₐ[ℚ] C) (x : 𝓞 E), ∃ y : O,
      algebraMap O C y = φ (algebraMap (𝓞 E) E x) := by
    intro φ x
    have h1 : IsIntegral ℤ (φ (algebraMap (𝓞 E) E x)) :=
      (x.isIntegral_coe).map (φ.toRingHom.toIntAlgHom)
    have h2 : IsIntegral O (φ (algebraMap (𝓞 E) E x)) := h1.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h2)
  choose F hF using hmem
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let e : ι ≃ (E →ₐ[ℚ] C) := Fintype.equivOfCardEq (by
    rw [AlgHom.card, Module.finrank_eq_card_basis (integralBasis E)])
  let N : Matrix ι ι O := fun i j => F (e j) (RingOfIntegers.basis E i)
  have hN : (algebraMap O C).mapMatrix N =
      Algebra.embeddingsMatrixReindex ℚ C (integralBasis E) e := by
    ext i j
    show algebraMap O C (F (e j) (RingOfIntegers.basis E i)) = _
    simp [hF, Algebra.embeddingsMatrixReindex, integralBasis_apply]
  have hdisc : ((NumberField.discr E : ℤ) : O) = N.det ^ 2 := by
    apply hinj
    rw [map_pow, RingHom.map_det, hN, ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two,
      ← NumberField.coe_discr]
    simp
  have hdet : N.det ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    apply Matrix.det_zero_of_column_eq (i := e.symm τ) (j := e.symm τ')
      (fun h => hττ (e.symm.injective h))
    intro k
    show residue O (F (e (e.symm τ)) (RingOfIntegers.basis E k)) =
      residue O (F (e (e.symm τ')) (RingOfIntegers.basis E k))
    simp only [Equiv.apply_symm_apply]
    have a1 : F τ (RingOfIntegers.basis E k) = σ (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ])
    have a2 : F τ' (RingOfIntegers.basis E k) = σ' (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ'])
    rw [a1, a2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hcong _
  have hdm : ((NumberField.discr E : ℤ) : O) ∈ maximalIdeal O := by
    rw [hdisc]
    exact Ideal.pow_mem_of_mem _ hdet 2 (by norm_num)
  have hpm : (p : O) ∈ maximalIdeal O := hpu
  have hcop : IsCoprime (p : ℤ) (NumberField.discr E) :=
    (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : O) ∈ maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddCurve

section Rings
variable (R : Type) [CommRing R] (l : ℕ)

abbrev Tr : Type := AdjoinRoot (Polynomial.X ^ l : Polynomial R)

variable {R l}

def cf (n : ℕ) : Tr R l →ₗ[R] R := (Polynomial.lcoeff R n).comp (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow l))

variable (R l)

end Rings

section Points
variable {k : Type} [CommRing k]

variable {B : Over (Spec (CommRingCat.of k))}

variable {R : Type} [CommRing R] [Algebra k R]

end Points

end GlobalTheory.AddCurve
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace GlobalTheory.CurveJet

variable {C : Type} [Field C] {dd m : ℕ}

def inT (σ : Type) (f : PowerSeries C) : MvPowerSeries (Option σ) C :=
  MvPowerSeries.subst (fun _ : Unit => (X none : MvPowerSeries (Option σ) C)) f

theorem inT_eq_rename (σ : Type) (f : PowerSeries C) :
    inT σ f = rename (fun _ : Unit => (none : Option σ)) f := by
  rw [inT, rename_eq_subst]
  rfl

theorem constantCoeff_inT (σ : Type) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (inT σ f) = 0 := by
  rw [inT_eq_rename, constantCoeff_rename]
  exact hf

theorem optionEquivLeft_inT (σ : Type) (f : PowerSeries C) :
    optionEquivLeft σ C (inT σ f) = PowerSeries.map (MvPowerSeries.C : C →+* MvPowerSeries σ C) f := by
  classical
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_map, coeff_C, inT_eq_rename]
  split_ifs with hμ
  · subst hμ
    let e : Unit ↪ Option σ := ⟨fun _ => none, fun _ _ _ => rfl⟩
    have he : Finsupp.optionElim n (0 : σ →₀ ℕ) = Finsupp.embDomain e (Finsupp.single () n) := by
      rw [Finsupp.embDomain_single, Finsupp.optionElim_zero]
      rfl
    rw [he]
    exact coeff_embDomain_rename e f (Finsupp.single () n)
  · apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hμ
    ext s
    have h1 : Finsupp.mapDomain (fun _ : Unit => (none : Option σ)) y (some s) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_some] at h1
    simpa using h1

theorem optionEquivLeft_rename_some {σ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    optionEquivLeft σ C (rename (some : σ → Option σ) f) = PowerSeries.C f := by
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    have he : Finsupp.optionElim 0 μ = Finsupp.embDomain (Function.Embedding.some) μ := by
      ext t
      cases t <;> simp
    rw [he]
    exact coeff_embDomain_rename _ f μ
  · rw [map_zero]
    apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hn
    have h1 : Finsupp.mapDomain (some : σ → Option σ) y none = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_none] at h1
    exact h1

theorem pderiv_coeff_optionEquivLeft {σ : Type} (f : MvPowerSeries (Option σ) C) (n : ℕ) (s : σ) :
    pderiv s (PowerSeries.coeff n (optionEquivLeft σ C f)) =
      PowerSeries.coeff n (optionEquivLeft σ C (pderiv (some s) f)) := by
  classical
  ext μ
  rw [coeff_pderiv, coeff_coeff_optionEquivLeft, coeff_coeff_optionEquivLeft, coeff_pderiv]
  have key : Finsupp.optionElim n (μ + Finsupp.single s 1) =
      Finsupp.optionElim n μ + Finsupp.single (some s) 1 := by
    ext t
    cases t <;> simp [Finsupp.single_apply]
  rw [key, Finsupp.optionElim_apply_some]

end GlobalTheory.CurveJet
end
end
