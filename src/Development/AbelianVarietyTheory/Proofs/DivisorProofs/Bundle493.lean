module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle331
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle443
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle444
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle445
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.Topology.LocallyConstant.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle446
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.HatInd

theorem inPar_gal {F' : Type} [Field F'] (u : F' →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F') :
    InPar a (gal u n x) ↔ InPar a x := by
  unfold InPar gal
  simp only [Matrix.GeneralLinearGroup.map_apply, map_eq_zero]

theorem par_facts {F' : Type} [Field F'] (a b n : ℕ) (h : n = a + b) :
    (∀ x y : GL (Fin n) F', InPar a x → InPar a y → InPar a (x * y)) ∧ InPar a (1 : GL (Fin n) F') ∧
    (∀ x : GL (Fin n) F', InPar a x → InPar a x⁻¹) ∧
    (∀ x y : GL (Fin n) F', InPar a x → InPar a y → tlG a (x * y) = tlG a x * tlG a y) ∧
    (∀ x : GL (Fin n) F', InPar a x →
      ((tlG a x : GL (Fin a) F') : Matrix (Fin a) (Fin a) F') = tl a (x : Matrix (Fin n) (Fin n) F')) := by
  obtain ⟨H, π, hH, -, hπ, hmat, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n h
  refine ⟨fun x y hx hy => (hH _).1 (H.mul_mem ((hH x).2 hx) ((hH y).2 hy)), (hH 1).1 H.one_mem,
    fun x hx => (hH _).1 (H.inv_mem ((hH x).2 hx)), fun x y hx hy => ?_, fun x hx => ?_⟩
  · have := π.map_mul ⟨x, (hH x).2 hx⟩ ⟨y, (hH y).2 hy⟩
    rw [hπ, hπ, hπ] at this
    exact congrArg Prod.fst this
  · have := (hmat ⟨x, (hH x).2 hx⟩).1
    rw [hπ] at this
    exact this

theorem tlG_gal {F' : Type} [Field F'] (u : F' →+* F') (a b n : ℕ) (h : n = a + b) (x : GL (Fin n) F')
    (hx : InPar a x) : tlG a (gal u n x) = gal u a (tlG a x) := by
  have hm := (par_facts (F' := F') a b n h).2.2.2.2
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [hm _ ((inPar_gal u a x).2 hx)]
  unfold gal
  rw [Matrix.GeneralLinearGroup.map_apply, hm _ hx]
  unfold tl ent
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map_apply]

theorem finite_gal (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Finite (F' ≃ₐ[F] F') :=
  Finite.of_injective (fun e : F' ≃ₐ[F] F' => (e : F' → F')) (fun _ _ h => AlgEquiv.ext (congrFun h))

theorem galAct_symm {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (u : F' ≃ₐ[F] F')
    (x : GL (Fin n) F') : (galAct F F' n u).symm x = gal ((u⁻¹ : F' ≃ₐ[F] F') : F' →+* F') n x := rfl

theorem hat_ind : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (a b n : ℕ), n = a + b →
    ∀ X ∈ Virt ℂ ℂ (GHat F F' a), ∃ Z ∈ Virt ℂ ℂ (GHat F F' n), ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'),
      Z (inl δ * inr t) = hcTw (t : F' →+* F') a b (fun d => X (inl d * inr t)) (fun _ => 1) n δ := by
  intro F F' _ _ _ _ a b n hn X hX
  haveI : Finite (F' ≃ₐ[F] F') := finite_gal F F'
  haveI : Finite (GHat F F' n) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI : Finite (GHat F F' a) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  obtain ⟨hmul, hone, hinv, htl, -⟩ := par_facts (F' := F') a b n hn
  let P : Subgroup (GHat F F' n) :=
    { carrier := {x | InPar a x.left}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, mul_left, galAct_apply] at hx hy ⊢
        exact hmul _ _ hx ((inPar_gal _ a _).2 hy)
      one_mem' := by simpa using hone
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, inv_left, galAct_apply] at hx ⊢
        exact (inPar_gal _ a _).2 (hinv _ hx) }
  have hP : ∀ x : GHat F F' n, x ∈ P ↔ InPar a x.left := fun _ => Iff.rfl
  let πh : P →* GHat F F' a := MonoidHom.mk' (fun p => (⟨tlG a p.1.left, p.1.right⟩ : GHat F F' a))
    (fun p q => by
      have hp := (hP _).1 p.2
      have hq := (hP _).1 q.2
      apply SemidirectProduct.ext
      · simp only [Subgroup.coe_mul, mul_left, galAct_apply]
        rw [htl _ _ hp ((inPar_gal _ a _).2 hq), tlG_gal _ a b n hn _ hq]
      · simp)
  have hcl := (virt_mul_comap_conj_ind_linear (GHat F F' a)).2.2.1 X hX
  set ψ : P → ℂ := fun p => X (πh p) with hψ
  refine ⟨ind P ψ, (virt_mul_comap_conj_ind_linear (GHat F F' n)).2.2.2.1 P ψ
    ((virt_mul_comap_conj_ind_linear (GHat F F' a)).2.1 X hX P πh), fun t δ => ?_⟩

  have key : ∀ (w : GHat F F' n) (u : F' ≃ₐ[F] F'), ext0 P ψ ((inr u)⁻¹ * w * inr u) = ext0 P ψ w := by
    intro w u
    have hl : ((inr u)⁻¹ * w * inr u).left = gal ((u⁻¹ : F' ≃ₐ[F] F') : F' →+* F') n w.left := by
      simp [mul_left, galAct_apply, galAct_symm]
    have hr : ((inr u)⁻¹ * w * inr u).right = u⁻¹ * w.right * u := by simp
    unfold ext0
    by_cases hw : InPar a w.left
    · have hw' : (inr u)⁻¹ * w * inr u ∈ P := by rw [hP, hl]; exact (inPar_gal _ a _).2 hw
      rw [dite_eq_left hw', dite_eq_left ((hP w).2 hw)]
      simp only [hψ]
      have : πh ⟨(inr u)⁻¹ * w * inr u, hw'⟩ = (inr u)⁻¹ * πh ⟨w, (hP w).2 hw⟩ * inr u := by
        apply SemidirectProduct.ext
        · change tlG a ((inr u)⁻¹ * w * inr u).left = _
          rw [hl, tlG_gal _ a b n hn _ hw]
          simp [MonoidHom.mk'_apply, mul_left, galAct_apply, galAct_symm, πh]
        · change ((inr u)⁻¹ * w * inr u).right = _
          rw [hr]
          simp [MonoidHom.mk'_apply, πh]
      rw [this]
      have := hcl (πh ⟨w, (hP w).2 hw⟩) (inr u)
      simpa using this
    · have hw' : (inr u)⁻¹ * w * inr u ∉ P := by
        rw [hP, hl]; exact fun h => hw ((inPar_gal _ a _).1 h)
      rw [dite_eq_right hw', dite_eq_right (fun h => hw ((hP w).1 h))]
  haveI : Fintype (GHat F F' n) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin n) F') := Fintype.ofFinite _
  haveI : Fintype (F' ≃ₐ[F] F') := Fintype.ofFinite _
  set g : GHat F F' n := inl δ * inr t with hg
  have hval : ∀ y : GL (Fin n) F', ext0 P ψ ((inl y)⁻¹ * g * inl y) =
      if InPar a (y⁻¹ * δ * gal (t : F' →+* F') n y) then
        X (inl (tlG a (y⁻¹ * δ * gal (t : F' →+* F') n y)) * inr t) * 1 else 0 := by
    intro y
    have hl : ((inl y)⁻¹ * g * inl y).left = y⁻¹ * δ * gal (t : F' →+* F') n y := by
      simp [hg, mul_left, galAct_apply]
    have hr : ((inl y)⁻¹ * g * inl y).right = t := by simp [hg]
    unfold ext0
    by_cases hw : InPar a (y⁻¹ * δ * gal (t : F' →+* F') n y)
    · rw [dite_eq_left (by rw [hP, hl]; exact hw), if_pos hw, mul_one]
      simp only [hψ]
      congr 1
      apply SemidirectProduct.ext
      · change tlG a ((inl y)⁻¹ * g * inl y).left = _
        rw [hl]; simp
      · change ((inl y)⁻¹ * g * inl y).right = _
        rw [hr]; simp
    · rw [dite_eq_right (by rw [hP, hl]; exact hw), if_neg hw]
  have hz : ∀ (y : GL (Fin n) F') (u : F' ≃ₐ[F] F'),
      ((SemidirectProduct.equivProd (φ := galAct F F' n)).symm (y, u)) = inl y * inr u := by
    intro y u
    apply SemidirectProduct.ext <;> simp [SemidirectProduct.equivProd]
  have hsum : ∑ᶠ z : GHat F F' n, ext0 P ψ (z⁻¹ * g * z) =
      (Nat.card (F' ≃ₐ[F] F') : ℂ) * ∑ᶠ y : GL (Fin n) F', ext0 P ψ ((inl y)⁻¹ * g * inl y) := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← (SemidirectProduct.equivProd (φ := galAct F F' n)).symm.sum_comp, Fintype.sum_prod_type,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∀ u : F' ≃ₐ[F] F', ext0 P ψ ((inl y * inr u)⁻¹ * g * (inl y * inr u)) =
        ext0 P ψ ((inl y)⁻¹ * g * inl y) := by
      intro u
      have e : (inl y * inr u)⁻¹ * g * (inl y * inr u) = (inr u)⁻¹ * ((inl y)⁻¹ * g * inl y) * inr u := by
        simp only [mul_inv_rev, mul_assoc]
      rw [e, key]
    simp only [hz, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hcard : Nat.card P = Nat.card {p : GL (Fin n) F' // InPar a p} * Nat.card (F' ≃ₐ[F] F') := by
    rw [← Nat.card_prod]
    exact Nat.card_congr
      { toFun := fun p => (⟨p.1.left, p.2⟩, p.1.right)
        invFun := fun q => ⟨⟨q.1.1, q.2⟩, q.1.2⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  have hB : (Nat.card (F' ≃ₐ[F] F') : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := F' ≃ₐ[F] F')).ne'
  unfold ind hcTw
  rw [hcard, hsum]
  simp only [hval]
  push_cast
  rw [mul_inv, mul_assoc, ← mul_assoc _ (Nat.card (F' ≃ₐ[F] F') : ℂ), inv_mul_cancel₀ hB, one_mul]

end GlobalTheory.Shin.HatInd
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem wp_wpd_separate : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  intro N _ τ x y hx hy h1 h2
  obtain ⟨hsub, -, hmem, -, -⟩ := GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rw [wpd, wpd, div_left_inj' (pow_ne_zero _ hc)] at h2
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact (hsub x y).1 h
  · apply (hsub x y).1
    have e : tors N τ x = -tors N τ y + ((⟨_, h⟩ : (tauPair τ).lattice) : ℂ) := by
      simp
    have h3 : (tauPair τ).derivWeierstrassP (tors N τ x) =
        -(tauPair τ).derivWeierstrassP (tors N τ y) := by
      conv_lhs => rw [e]
      rw [PeriodPair.derivWeierstrassP_add_coe, PeriodPair.derivWeierstrassP_neg]
    have h0 : (tauPair τ).derivWeierstrassP (tors N τ y) = 0 := by
      rw [h2] at h3
      linear_combination h3 / 2
    have h4 := (Formalism.L2.Th1.F.pDerivZero (tauPair τ) _ hw).1 h0
    have h5 := (tauPair τ).lattice.sub_mem h h4
    convert h5 using 1
    ring

end GlobalTheory.WpFam
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (x : Fin 2 → ZMod N) (S : ℂ), 1 ≤ e → HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) S → ∃ T : ℂ, HasSum (fun k : ℕ => cSum N e ((-1) ^ (e + 1)) x k * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T ∧ S = (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1) else 0) + (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * T := by
  first | exact @GlobalTheory.WpFam.RowsSummed.main | exact GlobalTheory.WpFam.RowsSummed.main | (intros; apply GlobalTheory.WpFam.RowsSummed.main <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem adjoin_gen_eq_top {k F : Type} [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hm : (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) = k⟮x⟯ := by
    rw [IntermediateField.adjoin_map]; simp
  have hy : (y : F) ∈ (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) := by
    rw [hm]; exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

theorem val_lt_one_of_ord_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (t : F)
    (h : ord v t = 1) : v.1 t < 1 := by
  unfold ord at h
  by_cases h0 : v.1 t = 0
  · rw [h0] at h; simp at h
  · have hl : WithZero.log (v.1 t) < WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      simp; omega
    exact (WithZero.log_lt_log h0 one_ne_zero).1 hl

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem zeros_finite_sum_eq_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧
      ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  intro k F _ _ _ _ _ hF x hx
  haveI : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x hx
  set t : k⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ with ht
  have htx : algebraMap k⟮x⟯ F t = x := rfl
  have htr : Transcendental k t := by
    intro ha
    exact hx ((IntermediateField.isAlgebraic_iff).1 ha)
  have htop : k⟮t⟯ = ⊤ := adjoin_gen_eq_top x
  have hL : IsFF k k⟮x⟯ := by
    refine ⟨t, htr, ?_⟩
    rw [htop]
    have : Module.Free (⊤ : IntermediateField k k⟮x⟯) k⟮x⟯ :=
      Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top
  obtain ⟨v0, hv0, huniq⟩ := GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator k k⟮x⟯ t htr htop
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).1
  have ht0 : t ≠ 0 := by
    intro h; apply hx; rw [← htx, h, map_zero]; exact isAlgebraic_zero
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k k⟮x⟯ F hL ρ hρ v0 t ht0 hv0
  have hset : {v : Place k F | v.1 x < 1} = {p | ρ p = v0} := by
    ext p
    obtain ⟨e, he, hpow, -⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).2 ρ hρ p
    simp only [Set.mem_setOf_eq]
    change p.1 (algebraMap k⟮x⟯ F t) < 1 ↔ ρ p = v0
    rw [hpow t]
    constructor
    · intro h
      apply huniq
      by_contra hn
      exact absurd h (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))
    · intro h
      rw [h]
      exact pow_lt_one₀ zero_le' (val_lt_one_of_ord_eq_one v0 t hv0) he.ne'
  rw [hset]
  exact ⟨hfin, by simpa [htx] using hsum⟩

end GlobalTheory.Nef
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem finsum_ord_pull_eq_finrank_mul : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ
  classical
  have hunif : ∀ v : Place k F, ∃ π : F, π ≠ 0 ∧ ord v π = 1 := fun v => (GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.1
  choose π hπ0 hπ1 using hunif
  have hfib : ∀ v, {p | ρ p = v}.Finite ∧
      ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E (π v)) = Module.finrank F E :=
    fun v => GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k F E hFF ρ hρ v (π v) (hπ0 v) (hπ1 v)
  have hkey : ∀ p x, ord p (algebraMap F E x) = ord p (algebraMap F E (π (ρ p))) * ord (ρ p) x := by
    intro p x
    obtain ⟨e, -, -, he⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k F E).2 ρ hρ p
    rw [he x, he (π (ρ p)), hπ1, mul_one]
  have hpre : ∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite := by
    intro s hs
    have h : ρ ⁻¹' s = ⋃ v ∈ s, {p | ρ p = v} := by ext p; simp
    rw [h]; exact hs.biUnion fun v _ => (hfib v).1
  refine ⟨hpre, fun φ hφ => ?_⟩
  have hT := hpre _ hφ
  have hsupp : (Function.support fun p => ord p (algebraMap F E (φ (ρ p)))) ⊆ ↑hT.toFinset := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
    intro h; apply hp; rw [hkey, h, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [finsum_eq_sum_of_support_subset _ (s := hφ.toFinset) (by intro v hv; simpa using hv)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ρ) (t := hφ.toFinset) (by intro p hp; simpa using hp)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hc : ∀ p ∈ hT.toFinset.filter (fun p => ρ p = v),
      ord p (algebraMap F E (φ (ρ p))) = ord p (algebraMap F E (π v)) * ord v (φ v) := by
    intro p hp
    have hpv := (Finset.mem_filter.1 hp).2
    rw [hkey, hpv]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul]
  congr 1
  rw [← (hfib v).2, finsum_mem_eq_finite_toFinset_sum _ (hfib v).1]
  congr 1
  ext p
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hv, h⟩

end GlobalTheory.Nef
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem tsze_expand_fst_snd {g : ℕ} {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) :
        TrivSqZeroExt O (Fin g → O)).fst = h ∧
    ∀ b, (TrivSqZeroExt.inl h + ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) :
        TrivSqZeroExt O (Fin g → O)).snd b = v b := by
  rw [← tsze_expand]
  exact ⟨by simp, fun b ↦ by simp⟩

theorem jet_sh : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {l : Λ}
    {k k' : K.K} (e : K.le l k' k), ∃ χ : K.jet k ⟶ K.jet k', χ.deg = l ∧
      jet0 k ≫ χ = ptHom (K.triv k') e ≫ jet0 k' ∧ jet1 k ≫ χ = ptHom (K.triv k') e ≫ jet1 k' ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        (TrivSqZeroExt.fst (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) = sh e x.fst) ∧
        ∀ a, TrivSqZeroExt.snd (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) a = sh e (x.snd a) := by
  intro I _ g Λ _ F K l k k' e
  have hf1 : ∀ y : Hol (K.W k), (ptHom (K.triv k') e ≫ jet0 k').φ y = TrivSqZeroExt.inl (sh e y) := fun y ↦ by
    change TrivSqZeroExt.inl (sh (K.le_refl k') (sh e y)) = _
    rw [sh_refl]
  have hf2 : ∀ y : Hol (K.W k), (ptHom (K.triv k') e ≫ jet1 k').φ y =
      TrivSqZeroExt.inl (sh e y) + TrivSqZeroExt.inr (fun a ↦ dw a (sh e y)) := fun y ↦ rfl
  obtain ⟨χ, hdeg, h0, h1, hφ⟩ := GlobalTheory.T.exists_jet_extension_square_zero K (T := K.jet k') (ptHom (K.triv k') e ≫ jet0 k')
    (ptHom (K.triv k') e ≫ jet1 k') (fun a ↦ TrivSqZeroExt.inr (Pi.single a 1)) rfl (fun _ ↦ rfl)
    (fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _) (fun x ↦ by
      rw [hf2, hf1]
      simp only [hf1]
      rw [tsze_expand]
      simp only [dw_sh])
  refine ⟨χ, hdeg.trans (add_zero l), h0, h1, fun x ↦ ?_⟩
  have hx : χ.φ x = TrivSqZeroExt.inl (sh e x.fst) +
      ∑ a, TrivSqZeroExt.inl (sh e (x.snd a)) * TrivSqZeroExt.inr (Pi.single a 1) := by
    rw [hφ, hf1]
    simp only [hf1]
  rw [hx]
  exact tsze_expand_fst_snd (sh e x.fst) (fun a ↦ sh e (x.snd a))

end GlobalTheory.AnPer.Charts
end
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc) (l : Λ), (∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ)) → ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = l → h _ _ f = h _ _ (ptHom T (Charts.Hom.le f)) := by
  first | exact @GlobalTheory.AnPer.Charts.cochain_eq_ptHom | exact GlobalTheory.AnPer.Charts.cochain_eq_ptHom | (intros; apply GlobalTheory.AnPer.Charts.cochain_eq_ptHom <;> assumption)
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.connectionForm_degZeroCocycle_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  first | exact @GlobalTheory.AnPer.ClosedSq.connForm_closed | exact GlobalTheory.AnPer.ClosedSq.connForm_closed | (intros; apply GlobalTheory.AnPer.ClosedSq.connForm_closed <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.freeRankOne_etaleSheaf_equiv_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∃ e : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R ≃+ Sec F U, (∀ U s (c : R), e U s (LocallyConstant.const U c) = (ULift.up c : ULift.{1} R) • Sec.res s g) ∧ ∀ (V U : Scheme.{0}) (j : V ⟶ U) (s : U ⟶ S) (φ : LocallyConstant U R), Sec.res j (e U s φ) = e V (j ≫ s) (φ.comap j.base.hom) := by
  first | exact @GlobalTheory.EtC.gen_locallyConstant | exact GlobalTheory.EtC.gen_locallyConstant | (intros; apply GlobalTheory.EtC.gen_locallyConstant <;> assumption)
end

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.linearMapFibreRank_split_comp_surjective : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] (K : Type) [AddCommGroup K] [Module O K] [Module.Finite O M] [Module.Finite O N] (f : M →ₗ[O] N), (∀ (ρ : N →ₗ[O] M), (∀ m, ρ (f m) = m) → ∀ q, fibreRank f q = fibreDim M q) ∧ (∀ (g : N →ₗ[O] K) (q : PrimeSpectrum O), fibreRank g q = fibreDim N q → fibreRank (g ∘ₗ f) q = fibreRank f q) ∧ ((∀ q, fibreRank f q = fibreDim N q) → Function.Surjective f) ∧ (∀ [Module.Free O M] (q : PrimeSpectrum O), fibreDim M q = Module.finrank O M) := by
  first | exact @GlobalTheory.FibreRanks.fibre_ranks | exact GlobalTheory.FibreRanks.fibre_ranks | (intros; apply GlobalTheory.FibreRanks.fibre_ranks <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X), Hyp R Φ a → ∀ n, WExact (term (Φ ⋙ HC R F) n) a := by
  first | exact @GlobalTheory.EtC.wExact_term_HC | exact GlobalTheory.EtC.wExact_term_HC | (intros; apply GlobalTheory.EtC.wExact_term_HC <;> assumption)
end
