module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.CobLin

theorem powerSeriesEvalTwoGroups_sub {R : Type} [CommRing R] {d : ℕ} {τ : Type} (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (c - c') u v = at2 c u v - at2 c' u v := by
  unfold at2
  exact subst_sub (hasSubst_of_constantCoeff_zero fun s => by
    cases s with
    | inl s => exact hu s
    | inr s => exact hv s) c c'

theorem constantCoeff_op_eq_zero {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 := by
  have ha : ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by
    cases s with
    | inl s => exact hu s
    | inr s => exact hv s
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha (hμ i)

theorem sub_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) → ∀ (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (f f' : MvPowerSeries (Fin d) R), cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧
    swap (c - c') = swap c - swap c' ∧ cob1 μ (f - f') = cob1 μ f - cob1 μ f' := by
  intro R _ d μ hμ c c' f f'
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  refine ⟨?_, ?_, ?_⟩
  · unfold cob2
    rw [powerSeriesEvalTwoGroups_sub c c' _ _ h2 h3, powerSeriesEvalTwoGroups_sub c c' _ _ (constantCoeff_op_eq_zero hμ _ _ h1 h2) h3,
      powerSeriesEvalTwoGroups_sub c c' _ _ h1 (constantCoeff_op_eq_zero hμ _ _ h2 h3), powerSeriesEvalTwoGroups_sub c c' _ _ h1 h2]
    abel
  · unfold swap
    exact powerSeriesEvalTwoGroups_sub c c' _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
  · unfold cob1 inL inR
    rw [subst_sub (hasSubst_of_constantCoeff_zero hμ),
      subst_sub (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_sub (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    abel

end GlobalTheory.CobLin
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

theorem _root_.GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  first | exact @GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | exact GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | (intros; apply GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

theorem _root_.GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  first | exact @GlobalTheory.BinomLeft.coeff_prod_pow_add | exact GlobalTheory.BinomLeft.coeff_prod_pow_add | (intros; apply GlobalTheory.BinomLeft.coeff_prod_pow_add <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

theorem _root_.GlobalTheory.T.coeff_prod_pow_x1_x2_add_x3 : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := by
  first | exact @GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups | exact GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups | (intros; apply GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.map_coboundary_swap_pullback_commute : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (S : Type) [CommRing S] (r : R →+* S), (∀ f, map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f)) ∧ (∀ c, map r (cob2 μ c) = cob2 (fun i => map r (μ i)) (map r c)) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, map r (Katz.swap c) = Katz.swap (map r c)) ∧ (∀ f : MvPowerSeries (Fin d) R, lin (map r f) = fun i => r (lin f i)) ∧ ∀ φ : Fin d → MvPowerSeries (Fin d) R, (∀ i, constantCoeff (φ i) = 0) → (∀ c, map r (pull2 φ c) = pull2 (fun i => map r (φ i)) (map r c)) ∧ ∀ f : MvPowerSeries (Fin d) R, map r (subst φ f) = subst (fun i => map r (φ i)) (map r f) := by
  first | exact @GlobalTheory.Katz.map_cob_swap_pull | exact GlobalTheory.Katz.map_cob_swap_pull | (intros; apply GlobalTheory.Katz.map_cob_swap_pull <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.coboundary_subst_eq_pullback_of_is_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), ∀ (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (φ : Fin d → MvPowerSeries (Fin d) R), (∀ i, constantCoeff (μ i) = 0) → (∀ i, constantCoeff (ν i) = 0) → IsHom μ ν φ → ∀ f : MvPowerSeries (Fin d) R, cob1 μ (subst φ f) = pull2 φ (cob1 ν f) := by
  first | exact @GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal | exact GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal | (intros; apply GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  first | exact @GlobalTheory.Katz.LawMonoid.mon | exact GlobalTheory.Katz.LawMonoid.mon | (intros; apply GlobalTheory.Katz.LawMonoid.mon <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SwapCoeff

theorem swap_eq_rename (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap c = rename (Equiv.sumComm (Fin d) (Fin d)) c := by
  rw [rename_eq_subst]
  unfold swap at2
  congr 1
  funext s
  rcases s with i | i <;> rfl

theorem coeff_swap : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a e) (swap c) = coeff (Finsupp.sumElim e a) c := by
  intro R _ d c a e
  have h := coeff_embDomain_rename (Equiv.sumComm (Fin d) (Fin d)).toEmbedding c (Finsupp.sumElim e a)
  have hinj : Function.Injective (Equiv.sumComm (Fin d) (Fin d)) := (Equiv.sumComm _ _).injective
  have hE : Finsupp.embDomain (Equiv.sumComm (Fin d) (Fin d)).toEmbedding (Finsupp.sumElim e a) =
      Finsupp.sumElim a e := by
    rw [Finsupp.embDomain_eq_mapDomain]
    ext x
    rcases x with i | i
    · have := Finsupp.mapDomain_apply_of_injective hinj (Finsupp.sumElim e a) (Sum.inr i)
      simpa using this
    · have := Finsupp.mapDomain_apply_of_injective hinj (Finsupp.sumElim e a) (Sum.inl i)
      simpa using this
  rw [hE] at h
  rw [swap_eq_rename]
  exact h

end GlobalTheory.SwapCoeff
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Obs.TrivAug

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem mul_eq_of_map_eq {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hk : RingHom.ker π = I)
    {a b : R} (h : π a = π b) (i : I) : a * (i : R) = b * i := by
  have h1 : a - b ∈ I := hk ▸ (RingHom.mem_ker.2 (by rw [map_sub, h, sub_self]))
  have h2 : (a - b) * (i : R) ∈ I ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul h1 i.2
  rw [hI, Ideal.zero_eq_bot, Ideal.mem_bot, sub_mul, sub_eq_zero] at h2
  exact h2

def smulI (I : Ideal R) {π : R →+* R₀} (hπ : Function.Surjective π) : SMul R₀ I :=
  ⟨fun r i => ⟨Function.surjInv hπ r * i, I.mul_mem_left _ i.2⟩⟩

def modI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ I :=
  @Function.Surjective.moduleLeft R R₀ I _ _ _ _ (smulI I hπ) π hπ (fun c x => by
    apply Subtype.ext
    show Function.surjInv hπ (π c) * (x : R) = c * x
    exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π c)) x)

def modOpI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ᵐᵒᵖ I :=
  letI := modI hI hπ hk
  Module.compHom I (RingEquiv.toOpposite R₀).symm.toRingHom

end GlobalTheory.Obs.TrivAug
end

open GlobalTheory.Obs.TrivAug in
theorem GlobalTheory.Obs.exists_aug : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁), Nonempty (Aug I π R₁) := by
  intro R R₀ _ _ I hI π hπ hk
  letI : Module R₀ I := modI hI hπ hk
  letI : Module R₀ᵐᵒᵖ I := modOpI hI hπ hk
  haveI : IsCentralScalar R₀ I := ⟨fun r m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (MulOpposite.op r)) * (m : R) = Function.surjInv hπ r * m
    rfl⟩
  haveI : IsScalarTower R₀ R₀ᵐᵒᵖ I := ⟨fun r s m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (r • s)) * (m : R) = Function.surjInv hπ r * (Function.surjInv hπ (MulOpposite.unop s) * m)
    rw [← _root_.mul_assoc]
    refine mul_eq_of_map_eq hI hk ?_ m
    simp [Function.surjInv_eq hπ, smul_eq_mul, mul_comm]⟩
  refine ⟨TrivSqZeroExt R₀ I, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
  { q := TrivSqZeroExt.fstHom R₀ R₀ I
    k := { toFun := fun y => (y.snd : R), map_zero' := rfl, map_add' := fun _ _ => rfl }
    mem := fun y => y.snd.2
    smul := fun r y => by
      show Function.surjInv hπ (π r) * (y.snd : R) = r * y.snd
      exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π r)) _
    one := rfl
    sq := fun y y' h h' => by
      have h0 : y.fst = 0 := h
      have h0' : y'.fst = 0 := h'
      ext
      · simp [h0]
      · simp [h0, h0']
    inj := fun y h h' => by
      have h0 : y.fst = 0 := h
      ext
      · exact h0
      · have h1 : (y.snd : R) = 0 := h'
        rw [h1]; rfl
    surj := fun i hi => ⟨TrivSqZeroExt.inr ⟨i, hi⟩, rfl, rfl⟩ }
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.SigInj

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)

def jj (i : I) : R₁ := Classical.choose (α.surj i.1 i.2)

theorem jj_q (i : I) : α.q (jj α i) = 0 := (Classical.choose_spec (α.surj i.1 i.2)).1

theorem jj_k (i : I) : α.k (jj α i) = i := (Classical.choose_spec (α.surj i.1 i.2)).2

theorem eq_jj {y : R₁} {i : I} (hq : α.q y = 0) (hk : α.k y = i) : y = jj α i := by
  have h := α.inj (y - jj α i) (by rw [map_sub, hq, jj_q, sub_zero]) (by rw [map_sub, hk, jj_k, sub_self])
  exact sub_eq_zero.mp h

theorem jj_add (i i' : I) : jj α (i + i') = jj α i + jj α i' :=
  (eq_jj α (by rw [map_add (f := _), jj_q, jj_q, add_zero]) (by rw [map_add (f := _), jj_k, jj_k]; rfl)).symm

theorem jj_smul (r : R) (i : I) : jj α (r • i) = π r • jj α i :=
  (eq_jj α (by rw [map_smul, jj_q, smul_zero]) (by rw [α.smul, jj_k]; rfl)).symm

variable {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀)

def tau (hs : SemiHom π p) : I ⊗[R] B →+ R₁ ⊗[R₀] B₀ :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun i ↦ AddMonoidHom.mk' (fun b ↦ jj α i ⊗ₜ[R₀] p b)
      (fun b b' ↦ by rw [map_add (f := _), TensorProduct.tmul_add]))
      (fun i i' ↦ by ext b; simp [jj_add, TensorProduct.add_tmul]))
    (fun r i b ↦ by
      simp only [AddMonoidHom.mk'_apply]
      rw [jj_smul, hs r b, TensorProduct.smul_tmul])

theorem tau_tmul (hs : SemiHom π p) (i : I) (b : B) : tau α p hs (i ⊗ₜ b) = jj α i ⊗ₜ[R₀] p b := by
  simp [tau, TensorProduct.liftAddHom_tmul]

end GlobalTheory.Obs.SigInj

open GlobalTheory.Obs.SigInj in
theorem GlobalTheory.Obs.sig_inj_of_flat : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) [Module.Flat R B] (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → ∀ y, α.KerQ y → σ y = 0 → y = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker _ σ hσ y hy h0
  have hrange : ∀ y : R₁ ⊗[R₀] B₀, ∃ z, tau α p hs z =
      y - (1 : R₁) ⊗ₜ[R₀] TensorProduct.lid R₀ B₀ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      have hq' : α.q (x - algebraMap R₀ R₁ (α.q x)) = 0 := by simp
      refine ⟨⟨α.k (x - algebraMap R₀ R₁ (α.q x)), α.mem _⟩ ⊗ₜ b, ?_⟩
      rw [tau_tmul, ← eq_jj α hq' rfl, Algebra.TensorProduct.map_tmul, TensorProduct.lid_tmul,
        ← TensorProduct.smul_tmul, TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one]
      rfl
    | add a c ha hc =>
      obtain ⟨za, hza⟩ := ha
      obtain ⟨zc, hzc⟩ := hc
      exact ⟨za + zc, by rw [map_add (f := _), hza, hzc, map_add (f := _), map_add (f := _), TensorProduct.tmul_add]; abel⟩
  obtain ⟨z, hz⟩ := hrange y
  rw [show Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y = 0 from hy, map_zero,
    TensorProduct.tmul_zero, sub_zero] at hz
  have hμ : ∀ z, σ (tau α p hs z) = TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul i b => rw [tau_tmul, hσ, jj_k]; simp
    | add a c ha hc => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hc]
  have hinj : Function.Injective (fun z ↦ TensorProduct.lid R B (LinearMap.rTensor B I.subtype z)) :=
    (TensorProduct.lid R B).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hz0 : z = 0 := hinj (by
    show TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) =
      TensorProduct.lid R B (LinearMap.rTensor B I.subtype 0)
    rw [map_zero, map_zero, ← hμ, hz, h0])
  rw [← hz, hz0, map_zero]
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem sig_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (ρ : B →ₐ[R] B') (φ : B₀ →ₐ[R₀] B₀'), (∀ b, p' (ρ b) = φ (p b)) → ∀ (σ : R₁ ⊗[R₀] B₀ →+ B) (σ' : R₁ ⊗[R₀] B₀' →+ B'), α.IsSig p σ → α.IsSig p' σ' → (∀ y, ρ (σ y) = σ' (extHom R₁ φ y)) ∧ ∀ y, α.KerQ y → α.KerQ (extHom R₁ φ y) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' ρ φ hρ σ σ' hσ hσ'
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      rw [hσ r b]
      simp only [extHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← hρ b, hσ' r (ρ b), map_smul]
    | add x z hx hz => simp only [map_add (f := _), hx, hz]
  · have key : ∀ y : R₁ ⊗[R₀] B₀,
        Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀') (extHom R₁ φ y) =
          Algebra.TensorProduct.map (AlgHom.id R₀ R₀) φ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b₀ => simp [extHom]
      | add x z hx hz => simp only [map_add (f := _), hx, hz]
    unfold Aug.KerQ at hy ⊢
    rw [key, hy, map_zero]

end GlobalTheory.Obs
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem Obs.sig_basic : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker σ hσ
  have h2 : ∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← map_mul, hσ, hσ, mul_smul_comm]
    | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  refine ⟨?_, h2, ?_, ?_⟩
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [hσ, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem y'))
    | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
  · intro b₀
    obtain ⟨b', rfl⟩ := hp b₀
    rw [hσ, α.one, zero_smul]
  · intro x hx
    rw [Ideal.map, Ideal.span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨y, hy0, hyk⟩ := α.surj i hi
      refine ⟨y ⊗ₜ 1, ?_, ?_⟩
      · simp [Obs.Aug.KerQ, hy0]
      · rw [← map_one p, hσ, hyk, Algebra.smul_def, _root_.mul_one]
    | zero => exact ⟨0, by simp [Obs.Aug.KerQ], by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      refine ⟨y + y', ?_, by rw [map_add (f := _)]⟩
      simp only [Obs.Aug.KerQ, map_add (f := _)] at *; rw [hy, hy', add_zero]
    | smul b x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨(1 ⊗ₜ p b) * y, ?_, by rw [h2, smul_eq_mul]⟩
      simp only [Obs.Aug.KerQ, map_mul] at *; rw [hy, mul_zero]

end GlobalTheory
end
