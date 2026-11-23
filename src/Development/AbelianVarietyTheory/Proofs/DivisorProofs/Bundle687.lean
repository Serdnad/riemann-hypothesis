module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.TensPres

variable {k : Type} [CommRing k]

def ordIdeal (ρ : Type) (N : ℕ) : Ideal (MvPowerSeries ρ k) where
  carrier := {f | (N : ℕ∞) ≤ f.order}
  add_mem' {f g} hf hg := MvPowerSeries.le_order fun d hd => by
    rw [map_add (f := _), MvPowerSeries.coeff_of_lt_order (hd.trans_le hf),
      MvPowerSeries.coeff_of_lt_order (hd.trans_le hg), add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    change (N : ℕ∞) ≤ (c * f).order
    exact hf.trans (le_add_self.trans (MvPowerSeries.le_order_mul (f := c) (g := f)))

theorem mem_ordIdeal_order {ρ : Type} {N : ℕ} {f : MvPowerSeries ρ k} :
    f ∈ ordIdeal (k := k) ρ N ↔ (N : ℕ∞) ≤ f.order := Iff.rfl

theorem mem_ordIdeal {ρ : Type} {N : ℕ} {f : MvPowerSeries ρ k} :
    f ∈ ordIdeal (k := k) ρ N ↔ ∀ α : ρ →₀ ℕ, α.degree < N → coeff α f = 0 := by
  constructor
  · intro h α hα
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.2 hα) ((mem_ordIdeal_order).1 h))
  · intro h
    exact (mem_ordIdeal_order).2 (MvPowerSeries.nat_le_order h)

theorem one_le_order_X {ρ : Type} (t : ρ) : (1 : ℕ∞) ≤ (X t : MvPowerSeries ρ k).order := by
  have := MvPowerSeries.nat_le_order (f := (X t : MvPowerSeries ρ k)) (n := 1) fun d hd => by
    have : d = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]; omega
    subst this; simp
  exact_mod_cast this

theorem subst_mem_ordIdeal {ρ ρ' : Type} [Finite ρ] (e : ρ → ρ') {N : ℕ}
    {f : MvPowerSeries ρ k} (hf : f ∈ ordIdeal (k := k) ρ N) :
    subst (fun i => (X (e i) : MvPowerSeries ρ' k)) f ∈ ordIdeal (k := k) ρ' N := by
  have ha : HasSubst (fun i => (X (e i) : MvPowerSeries ρ' k)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_X _
  have h1 : (1 : ℕ∞) ≤ ⨅ i, ((fun i => (X (e i) : MvPowerSeries ρ' k)) i).order :=
    le_iInf fun i => one_le_order_X (e i)
  have h2 := MvPowerSeries.le_order_subst ha f
  refine (mem_ordIdeal_order).2 ?_
  calc (N : ℕ∞) ≤ f.order := (mem_ordIdeal_order).1 hf
    _ = 1 * f.order := (one_mul _).symm
    _ ≤ _ := by gcongr
    _ ≤ _ := h2

end GlobalTheory.TensPres


open GlobalTheory.TensPres in
theorem GlobalTheory.evA_tensor_presents : ∀ (k : Type) [CommRing k] (σ τ : Type) [Finite σ] [Finite τ] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : τ → B) (hy : ∀ i, IsNilpotent (y i)) (hz : ∀ i, IsNilpotent (Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) i)), Function.Surjective (evA k x hx) → Function.Surjective (evA k y hy) → Function.Surjective (evA k _ hz) ∧ ∀ N : ℕ, (∀ f, evA k x hx f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (∀ f, evA k y hy f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ f, evA k _ hz f = 0 → ∀ α : (σ ⊕ τ) →₀ ℕ, α.degree < N → coeff α f = 0 := by
  intro k _ σ τ _ _ A B _ _ _ _ x hx y hy hz hsx hsy
  have hX : ∀ t, evA k _ hz (X t) =
      Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) t :=
    fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k (σ ⊕ τ) (A ⊗[k] B) _ hz t
  have hzX : ∀ t, IsNilpotent (evA k _ hz (X t)) := fun t => by rw [hX]; exact hz t
  have hxl : ∀ i, IsNilpotent (x i ⊗ₜ[k] (1 : B)) := fun i => hz (Sum.inl i)
  have hyr : ∀ j, IsNilpotent ((1 : A) ⊗ₜ[k] y j) := fun j => hz (Sum.inr j)
  have hL : ∀ f : MvPowerSeries σ k,
      evA k _ hz (subst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) f) =
        evA k x hx f ⊗ₜ[k] (1 : B) := by
    intro f
    rw [(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ (A ⊗[k] B)).1 (σ ⊕ τ) (evA k _ hz) hzX _
      (fun i => constantCoeff_X _) _ hxl (fun i => by rw [hX]; rfl) f]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ A).2 (A ⊗[k] B) (Algebra.TensorProduct.includeLeft (S := k))
      x hx _ hxl (fun i => rfl) f).symm
  have hR : ∀ g : MvPowerSeries τ k,
      evA k _ hz (subst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) g) =
        (1 : A) ⊗ₜ[k] evA k y hy g := by
    intro g
    rw [(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k τ (A ⊗[k] B)).1 (σ ⊕ τ) (evA k _ hz) hzX _
      (fun j => constantCoeff_X _) _ hyr (fun j => by rw [hX]; rfl) g]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k τ B).2 (A ⊗[k] B) Algebra.TensorProduct.includeRight
      y hy _ hyr (fun j => rfl) g).symm
  refine ⟨?_, ?_⟩
  · intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
      obtain ⟨f, rfl⟩ := hsx a
      obtain ⟨g, rfl⟩ := hsy b
      refine ⟨subst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) f *
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) g, ?_⟩
      rw [map_mul, hL, hR, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add u v hu hv =>
      obtain ⟨f, rfl⟩ := hu
      obtain ⟨g, rfl⟩ := hv
      exact ⟨f + g, map_add _ _ _⟩
  · intro N hNx hNy f hf α hα
    let J := ordIdeal (k := k) (σ ⊕ τ) N
    let mk := Ideal.Quotient.mkₐ k J
    have haL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have haR : HasSubst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    let φA : MvPowerSeries σ k →ₐ[k] _ := mk.comp (substAlgHom haL)
    let φB : MvPowerSeries τ k →ₐ[k] _ := mk.comp (substAlgHom haR)
    have hkA : ∀ g ∈ RingHom.ker (evA k x hx), φA g = 0 := by
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [φA, mk, AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact subst_mem_ordIdeal Sum.inl (mem_ordIdeal.2 (hNx g hg))
    have hkB : ∀ g ∈ RingHom.ker (evA k y hy), φB g = 0 := by
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [φB, mk, AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact subst_mem_ordIdeal Sum.inr (mem_ordIdeal.2 (hNy g hg))
    let ΨA : A →ₐ[k] _ := (Ideal.Quotient.liftₐ _ φA hkA).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsx).symm.toAlgHom
    let ΨB : B →ₐ[k] _ := (Ideal.Quotient.liftₐ _ φB hkB).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsy).symm.toAlgHom
    have hΨA : ∀ g, ΨA (evA k x hx g) = φA g := by
      intro g
      have : (Ideal.quotientKerAlgEquivOfSurjective hsx).symm (evA k x hx g) =
          Ideal.Quotient.mk _ g := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      change Ideal.Quotient.liftₐ _ φA hkA ((Ideal.quotientKerAlgEquivOfSurjective hsx).symm (evA k x hx g)) = _
      rw [this]
      rfl
    have hΨB : ∀ g, ΨB (evA k y hy g) = φB g := by
      intro g
      have : (Ideal.quotientKerAlgEquivOfSurjective hsy).symm (evA k y hy g) =
          Ideal.Quotient.mk _ g := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      change Ideal.Quotient.liftₐ _ φB hkB ((Ideal.quotientKerAlgEquivOfSurjective hsy).symm (evA k y hy g)) = _
      rw [this]
      rfl
    let Ψ := Algebra.TensorProduct.lift ΨA ΨB (fun _ _ => Commute.all _ _)
    have hnil : ∀ t, IsNilpotent (mk (X t)) := by
      intro t
      refine ⟨N, ?_⟩
      rw [← map_pow]
      simp only [mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      refine (mem_ordIdeal_order).2 ?_
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • (X t : MvPowerSeries (σ ⊕ τ) k).order := by gcongr; exact one_le_order_X t
        _ ≤ _ := MvPowerSeries.le_order_pow _
    have huniq := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (σ ⊕ τ) _ mk (Ψ.comp (evA k _ hz)) hnil (by
      intro t
      rw [AlgHom.comp_apply, hX]
      cases t with
      | inl i =>
        simp only [Sum.elim_inl, Ψ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        rw [← GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A x hx i, hΨA]
        simp only [φA, AlgHom.comp_apply, coe_substAlgHom, subst_X haL]
      | inr j =>
        simp only [Sum.elim_inr, Ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rw [← GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k τ B y hy j, hΨB]
        simp only [φB, AlgHom.comp_apply, coe_substAlgHom, subst_X haR])
    have hmk : mk f = 0 := by
      rw [huniq, AlgHom.comp_apply, hf, map_zero]
    simp only [mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hmk
    exact mem_ordIdeal.1 hmk α hα
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.EvSquare

noncomputable def constAlg (σ : Type) (k : Type) [CommRing k] : MvPowerSeries σ k →ₐ[k] k :=
  { (constantCoeff : MvPowerSeries σ k →+* k) with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

theorem evA_zero (k : Type) [CommRing k] (σ : Type) [Finite σ] (f : MvPowerSeries σ k) :
    evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero) f = constantCoeff f := by
  have h := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ k (evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero))
    (constAlg σ k) (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact IsNilpotent.zero)
    (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; simp [constAlg])
  rw [h]; rfl

theorem main : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ n, (∀ f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[k] 1) ∧ (∀ f, c.ev₂ n (inR f) = 1 ⊗ₜ[k] c.ev n f) ∧ (∀ s, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s)) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n)) (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  intro p k _ d G c n
  have hX : ∀ t, c.ev₂ n (X t) = c.x₂ n t := fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate _ _ _ _ _ t
  have hN : ∀ t, IsNilpotent (c.ev₂ n (X t)) := fun t => by rw [hX]; exact c.nil₂ n t
  refine ⟨fun f => ?_, fun f => ?_, fun s => ?_, fun s => ?_⟩
  · have hy : ∀ i, IsNilpotent (c.x n i ⊗ₜ[k] (1 : G.A n)) := fun i => c.nil₂ n (Sum.inl i)
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (fun i => X (Sum.inl i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      Algebra.TensorProduct.includeLeft (c.x n) (c.nil n) _ hy (fun i => rfl) f
    unfold inL; rw [e1, ← e2]; rfl
  · have hy : ∀ i, IsNilpotent ((1 : G.A n) ⊗ₜ[k] c.x n i) := fun i => c.nil₂ n (Sum.inr i)
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (fun i => X (Sum.inr i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      Algebra.TensorProduct.includeRight (c.x n) (c.nil n) _ hy (fun i => rfl) f
    unfold inR; rw [e1, ← e2]; rfl
  · let g : G.A n ⊗[k] G.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      (Algebra.TensorProduct.comm k (G.A n) (G.A n)).toAlgHom
    have hy : ∀ i, IsNilpotent (g (c.x₂ n i)) := fun i => (c.nil₂ n i).map g
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)))
      (fun i => by cases i <;> exact constantCoeff_X _) _ hy
      (fun i => by
        cases i with
        | inl i => rw [Sum.elim_inl, hX]; simp [g, Chart.x₂]
        | inr i => rw [Sum.elim_inr, hX]; simp [g, Chart.x₂]) s
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 (G.A n ⊗[k] G.A n)
      g (c.x₂ n) (c.nil₂ n) _ hy (fun i => rfl) s
    unfold Katz.swap at2
    rw [e1, ← e2]; rfl
  · let L : G.A n ⊗[k] G.A n →ₐ[k] k := Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n))
      (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _)
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 k
      L (c.x₂ n) (c.nil₂ n) (fun _ => (0 : k)) (fun _ => IsNilpotent.zero)
      (fun i => by
        cases i with
        | inl i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]
        | inr i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]) s
    change L (c.ev₂ n s) = _
    unfold Chart.ev₂; rw [e2, evA_zero]

end GlobalTheory.EvSquare
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma le_one_and_mem_latM_of_hasLevel {F : Type} [Field F] [NumberField F] {N : ℕ}
    {A B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {x : F}
    (h : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split A B x)) :
    ((B : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) ∧ (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A ∧
      (N : F) * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A := by
  obtain ⟨h1, h2⟩ := h
  have mem : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.split A B x ↔
      v 0 ∈ (B : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A :=
    fun v ↦ Iff.rfl
  have std : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.stdLat F ↔
      ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := by
    intro v; simp [_root_.GlobalTheory.HilbFam.stdLat, Submodule.mem_pi]
  have one_mem : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have zero_mem' : (0 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.zero_mem _
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    have hv : ![b, b * x] ∈ _root_.GlobalTheory.HilbFam.split A B x :=
      (mem _).2 ⟨by simpa using hb, by
        simpa using FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)⟩
    have := ((std _).1 (h2 hv)) 0
    simp only [Matrix.cons_val_zero] at this
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨y, hy⟩
  · have hv := h1 ![0, 1] ((std _).2 (by intro i; fin_cases i <;> simpa))
    have := ((mem _).1 hv).2
    simpa [Algebra.smul_def] using this
  · have hv := h1 ![1, 0] ((std _).2 (by intro i; fin_cases i <;> simpa))
    have := FractionalIdeal.mem_coe.1
      (Submodule.neg_mem _ (FractionalIdeal.mem_coe.2 ((mem _).1 hv).2))
    simpa [Algebra.smul_def] using this

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma mem_and_totally_pos_of_coeff_ne_zero {F : Type} [Field F] [NumberField F]
    {k N : ℕ} {A B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ} {x : F}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k A B a₀ a)
    (hN : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split A B x)) {ξ : F}
    (hξ0 : ξ ≠ 0) (hξ : a ξ ≠ 0) :
    ξ ∈ (A : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ := by
  obtain ⟨-, -, hsupp, -⟩ := ha
  obtain ⟨hmem, hpos⟩ := hsupp ξ hξ0 hξ
  refine ⟨?_, hpos⟩
  have hB := (le_one_and_mem_latM_of_hasLevel hN).1
  have hle : ((A * B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : FractionalIdeal (𝓞 F)⁰ F) ≤ A := by
    rw [Units.val_mul]
    calc (A : FractionalIdeal (𝓞 F)⁰ F) * B ≤ A * 1 := by gcongr
      _ = A := mul_one _
  exact hle hmem

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma sum_realEmbeddings_eq_trace {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] (y : F) :
    ∑ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i y = ((Algebra.trace ℚ F y : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  exact _root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace F y

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma trace_mul_int_of_mem_latM {F : Type} [Field F] [NumberField F]
    {A : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {y ξ : F} (hy : y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A)
    (hξ : ξ ∈ (A : FractionalIdeal (𝓞 F)⁰ F)) : ∃ c : ℤ, Algebra.trace ℚ F (y * ξ) = c := by
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual A.ne_zero] at hy
  obtain ⟨c, hc⟩ := hy ξ hξ
  exact ⟨c, by simpa [Algebra.traceForm_apply] using hc.symm⟩

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_support_trace_natCast_and_finite {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] {k : ℕ} {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ} {x : F}
    {N : ℕ} (hN : 0 < N) (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a)
    (hlev : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x)) :
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite := by
  have hNF : (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 := (le_one_and_mem_latM_of_hasLevel hlev).2.1
  have hpos : ∀ ξ, a ξ ≠ 0 → ξ ≠ 0 → ξ ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ := fun ξ hξ hξ0 ↦
    mem_and_totally_pos_of_coeff_ne_zero ha hlev hξ0 hξ

  have hbound : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) →
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) := by
    intro ξ hξ i
    rw [← sum_realEmbeddings_eq_trace]
    exact Finset.single_le_sum (fun j _ ↦ (hξ j).le) (Finset.mem_univ i)
  have htr_nonneg : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) →
      0 ≤ Algebra.trace ℚ F ξ := by
    intro ξ hξ
    have : (0 : ℝ) ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) := by
      rw [← sum_realEmbeddings_eq_trace]
      exact Finset.sum_nonneg fun j _ ↦ (hξ j).le
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · intro ξ hξ
    by_cases hξ0 : ξ = 0
    · exact ⟨0, by simp [hξ0]⟩
    obtain ⟨hmem, hξpos⟩ := hpos ξ hξ hξ0
    obtain ⟨c, hc⟩ := trace_mul_int_of_mem_latM hNF hmem
    have hc' : (N : ℚ) * Algebra.trace ℚ F ξ = c := by
      rw [← hc, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
    have hc0 : 0 ≤ c := by
      have : (0 : ℚ) ≤ c := hc' ▸ mul_nonneg (Nat.cast_nonneg _) (htr_nonneg ξ hξpos)
      exact_mod_cast this
    exact ⟨c.toNat, by rw [hc']; exact_mod_cast (Int.toNat_of_nonneg hc0).symm⟩
  · intro n
    obtain ⟨d, hd0, hd⟩ := (𝔞 : FractionalIdeal (𝓞 F)⁰ F).isFractional
    set D : F := algebraMap (𝓞 F) F d with hD
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0
    set M : ℝ := (∑ φ : F →+* ℂ, ‖φ D‖) * ((n : ℝ) / N) with hM
    have hfin := NumberField.Embeddings.finite_of_norm_le F ℂ M
    refine (hfin.image fun z ↦ z / D).subset ?_
    rintro ξ ⟨hξ, htr⟩
    refine ⟨D * ξ, ⟨?_, ?_⟩, by field_simp⟩
    · by_cases hξ0 : ξ = 0
      · simpa [hξ0] using isIntegral_zero
      obtain ⟨r, hr⟩ := hd ξ (hpos ξ hξ hξ0).1
      have hDξ : D * ξ = algebraMap (𝓞 F) F r := by rw [hr, Algebra.smul_def]
      rw [hDξ]
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro φ
      have hMnn : 0 ≤ M := by rw [hM]; positivity
      rw [map_mul, norm_mul]
      by_cases hξ0 : ξ = 0
      · simpa [hξ0] using hMnn
      have hξpos := (hpos ξ hξ hξ0).2
      have hφ := IsTotallyReal.complexEmbedding_isReal φ
      have htrq : Algebra.trace ℚ F ξ = n / N := by
        rw [eq_div_iff (by exact_mod_cast hN.ne')]
        rw [mul_comm]; exact htr
      have hφξ : ‖φ ξ‖ ≤ (n : ℝ) / N := by
        rw [← ComplexEmbedding.IsReal.coe_embedding_apply hφ, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hξpos _)]
        calc ComplexEmbedding.IsReal.embedding hφ ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) :=
              hbound ξ hξpos _
          _ = (n : ℝ) / N := by rw [htrq]; push_cast; ring
      have hφD : ‖φ D‖ ≤ ∑ ψ : F →+* ℂ, ‖ψ D‖ :=
        Finset.single_le_sum (fun ψ _ ↦ norm_nonneg (ψ D)) (Finset.mem_univ φ)
      rw [hM]
      exact mul_le_mul hφD hφξ (norm_nonneg _) (Finset.sum_nonneg fun ψ _ ↦ norm_nonneg _)


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.coef_support_trace : ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F)
    (N : ℕ), 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a →
    _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) →
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite :=
  fun _ _ _ _ _ _ _ _ _ _ _ hN ha hlev ↦ coeff_support_trace_natCast_and_finite hN ha hlev

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.laguerreSignedBinomCoeff_mul : ∀ k n m j : ℕ, j ≤ m → m ≤ n → rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  first | exact @GlobalTheory.HilbFam.rco_mul_rco | exact GlobalTheory.HilbFam.rco_mul_rco | (intros; apply GlobalTheory.HilbFam.rco_mul_rco <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.partialZeta_constTerm_eq_rational_value : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), 1 ≤ k → ZetaVals k z → IsPartialZeta C Z → (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) = ((z C / 2 ^ Module.finrank ℚ F : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.constTerm_eq_zetaVal | exact GlobalTheory.HilbFam.constTerm_eq_zetaVal | (intros; apply GlobalTheory.HilbFam.constTerm_eq_zetaVal <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.splitLattice_level_trace_denominator : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x ξ : F), HasLevel N (split 𝔞 𝔟 x) → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧ ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n := by
  first | exact @GlobalTheory.HilbFam.trace_denominator_of_hasLevel | exact GlobalTheory.HilbFam.trace_denominator_of_hasLevel | (intros; apply GlobalTheory.HilbFam.trace_denominator_of_hasLevel <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertLatticeTwist_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)), HasLevel N L → HasLevel N (twist N L α) := by
  first | exact @GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel | exact GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel | (intros; apply GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel <;> assumption)
end
