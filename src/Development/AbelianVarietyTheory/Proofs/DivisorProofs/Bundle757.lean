module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle715
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_rootSum_pair_prod_rootSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (m k l : ℕ) (e : Fin l → ℕ), 0 < m → ∑ᶠ x, psiG (rootSum θ k) m x * star (chG (fun P => ∏ j, rootSum θ (e j) P) m x) = (Nat.card (GL (Fin m) F) : ℂ) * ((Finset.univ.filter fun a : Fin l → Fin m => k ≡ ∑ j, e j * Nat.card F ^ (a j : ℕ) [MOD Nat.card F ^ m - 1]).card : ℂ) := by
  intro F _ _ θ hθ m k l e hm
  set q := Nat.card F with hq
  have hq1 : 1 < q := Finite.one_lt_card
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq1
  set N := q ^ m - 1 with hN
  have hN0 : 0 < N := by omega
  have hcast : ((q : ℂ) ^ m - 1) = ((N : ℕ) : ℂ) := by
    rw [hN, Nat.cast_sub hqm.le]; push_cast; ring
  have hNne : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have htor := GlobalTheory.T.green_function_character_sum F θ m k (fun P => ∏ j, rootSum θ (e j) P) hm
  have horth := (GlobalTheory.CuspGL.torus_orthogonality F θ hθ m hm).2
  set T := {α : AlgebraicClosure F | α ^ N = 1} with hT
  have hTfin : T.Finite := by
    apply (Polynomial.nthRoots N (1 : AlgebraicClosure F)).toFinset.finite_toSet.subset
    intro α hα
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hN0).2 hα
  have key : ∀ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    intro α hα
    have hr : ∀ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a : Fin m, θ α ^ (e j * q ^ (a : ℕ)) :=
      fun j => (GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range F θ m (e j) α hm hα).trans (Finset.sum_range (fun a => θ α ^ (e j * q ^ a)))
    simp_rw [hr]
    rw [← Finset.mul_sum, ← star_sum, Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ᶠ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, ∑ᶠ α ∈ T, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    rw [finsum_mem_congr rfl key, finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin]
  rw [hsum] at htor
  simp_rw [horth] at htor
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcast] at htor
  apply mul_left_cancel₀ hNne
  rw [htor]
  ring

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_GL_toLin' {F : Type} [Field F] (m : ℕ) (f : Module.End F (Fin m → F) → ℂ) :
    ∑ᶠ x : GL (Fin m) F, f (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) =
      ∑ᶠ g ∈ {g : Module.End F (Fin m → F) | IsUnit g}, f g := by
  rw [← finsum_mem_univ]
  refine finsum_mem_eq_of_bijOn
    (fun x : GL (Fin m) F => (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F) : Module.End F (Fin m → F)))
    ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro x _
    exact (Units.isUnit x).map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
  · intro x _ y _ h
    exact Units.ext (Matrix.toLin'.injective h)
  · intro g hg
    have h : IsUnit ((Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).symm g) := IsUnit.map _ hg
    refine ⟨h.unit, Set.mem_univ _, ?_⟩
    exact (Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).apply_symm_apply g

theorem finsum_cusp_mul_star_chG : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k l : ℕ, 0 < m → ∑ᶠ x, cusp θ m k x * star (chG (rootSum θ l) m x) = (-1) ^ (m - 1) * (Nat.card (GL (Fin m) F) : ℂ) * (((Finset.range m).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ m - 1)])).card : ℂ) := by
  intro F _ _ θ hθ m k l hm
  have hr : Module.finrank F (Fin m → F) = m := by simp
  have h := ipGL_psi_rootSum F (Fin m → F) θ hθ (by rw [hr]; exact hm) k l
  rw [hr, ipGL, ← finsum_GL_toLin', glCard] at h
  rw [mul_assoc, ← h, mul_finsum]
  refine finsum_congr fun x => ?_
  simp only [cusp, psiG, chG, Matrix.charpoly_toLin', mul_assoc]

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NormFibre

theorem card_conj_mul_card_commute {G : Type} [Group G] (g : G) :
    Nat.card {g' : G // IsConj g g'} * Nat.card {x : G // Commute x g} = Nat.card G := by
  have e1 : {g' : G // IsConj g g'} ≃ MulAction.orbit (ConjAct G) g :=
    Equiv.subtypeEquivRight (fun g' => by rw [ConjAct.mem_orbit_conjAct, isConj_comm])
  have e2 : {x : G // Commute x g} ≃ MulAction.stabilizer (ConjAct G) g :=
    { toFun := fun x => ⟨ConjAct.toConjAct x.1, by
          rw [MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul, x.2.eq, mul_inv_cancel_right]⟩
      invFun := fun y => ⟨ConjAct.ofConjAct y.1, by
          have h := y.2
          rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at h
          exact h⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) g),
    Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv.symm]

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem galAct_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    galAct F F' n t (incl F F' n γ) = incl F F' n γ := by
  ext i j
  simp [galAct_apply, gal, incl]

theorem galAct_coe (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  ext i j
  simp [galAct_apply, gal]

end Fields

section Count

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

def nrmFibreEquivOf (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (y : GL (Fin n) F') (hy : y * c * y⁻¹ = g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  have htw := (GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n).2.2.1
  { toFun := fun δ => ⟨y⁻¹ * δ.1 * galAct F F' n s y, by
        rw [htw, δ.2, ← hy]; group⟩
    invFun := fun ε => ⟨y * ε.1 * galAct F F' n s y⁻¹, by
        have := htw ε.1 y⁻¹
        rw [inv_inv] at this
        rw [this, ε.2, hy]⟩
    left_inv := fun δ => by
      apply Subtype.ext
      simp only [map_inv]
      group
    right_inv := fun ε => by
      apply Subtype.ext
      simp only [map_inv]
      group }

def nrmFibreEquiv (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (h : IsConj c g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  nrmFibreEquivOf s hs _ (isConj_iff.1 h).choose_spec

theorem card_isConj_nrm (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    (c : GL (Fin n) F') :
    Nat.card {δ : GL (Fin n) F' // IsConj c (nrm s δ)} =
      Nat.card {g' : GL (Fin n) F' // IsConj c g'} * Nat.card {δ : GL (Fin n) F' // nrm s δ = c} := by
  have e : {δ : GL (Fin n) F' // IsConj c (nrm s δ)} ≃
      Σ g' : {g' : GL (Fin n) F' // IsConj c g'}, {δ : GL (Fin n) F' // nrm s δ = g'.1} :=
    { toFun := fun δ => ⟨⟨nrm s δ.1, δ.2⟩, ⟨δ.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
      left_inv := fun δ => rfl
      right_inv := fun p => by
        rcases p with ⟨⟨g', hg⟩, ⟨δ, hδ⟩⟩
        dsimp only at hδ
        subst hδ
        rfl }
  rw [← Nat.card_prod]
  exact Nat.card_congr (e.trans ((Equiv.sigmaCongrRight fun g' => nrmFibreEquiv s hs g'.2).trans
    (Equiv.sigmaEquivProd _ _)))

end Count

section Centraliser

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem card_nrm_eq_mul_card_commute (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s)
    (n : ℕ) (γ : GL (Fin n) F) :
    Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} * Nat.card {x : GL (Fin n) F // Commute x γ} =
      Nat.card {x : GL (Fin n) F' // Commute x (incl F F' n γ)} := by
  obtain ⟨-, hinj, -, hcomm, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  obtain ⟨δ₀, hδ₀B, hδ₀⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hcfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t => galAct_incl n t γ
  set c := incl F F' n γ with hc
  set B := Subalgebra.centralizer F' {(c : Matrix (Fin n) (Fin n) F')} with hB
  have memB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B ↔ Commute x c := by
    intro x
    rw [hB, Subalgebra.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [Commute, SemiconjBy, Units.ext_iff, Units.val_mul, Units.val_mul]
    exact eq_comm
  have hcs : (c : Matrix (Fin n) (Fin n) F').map s = c := by rw [← galAct_coe, hcfix]
  have hstab : ∀ x ∈ B, x.map s ∈ B := by
    intro x hx
    rw [hB, Subalgebra.mem_centralizer_iff] at hx ⊢
    simp only [Set.mem_singleton_iff, forall_eq] at hx ⊢
    have e1 : ((c : Matrix (Fin n) (Fin n) F') * x).map s = ((c : Matrix (Fin n) (Fin n) F').map s) * x.map s :=
      Matrix.map_mul (f := (s : F' →+* F'))
    have e2 : (x * (c : Matrix (Fin n) (Fin n) F')).map s = x.map s * ((c : Matrix (Fin n) (Fin n) F').map s) :=
      Matrix.map_mul (f := (s : F' →+* F'))
    rw [hcs] at e1 e2
    rw [← e1, ← e2, hx]
  have h90 := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B hstab
  have hδ₀comm : ∀ e : GL (Fin n) F', Commute e c → Commute δ₀ e := by
    intro e he
    have hle : Algebra.adjoin F' {(c : Matrix (Fin n) (Fin n) F')} ≤
        Subalgebra.centralizer F' {(e : Matrix (Fin n) (Fin n) F')} := by
      apply Algebra.adjoin_le
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, ← Units.val_mul, ← Units.val_mul, he.eq]
    have h1 := hle hδ₀B
    rw [Subalgebra.mem_centralizer_iff] at h1
    have h2 := h1 _ rfl
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h2.symm)
  have hδ₀c : Commute δ₀ c := hδ₀comm c (Commute.refl c)
  have key : ∀ ε : GL (Fin n) F', Commute ε c → nrm s (δ₀ * ε) = c * nrm s ε := by
    intro ε hε
    rw [hmul δ₀ ε ?_, hδ₀]
    intro t u
    have h3 : Commute δ₀ (galAct F F' n (t⁻¹ * u) ε) := by
      apply hδ₀comm
      have := hε.map (galAct F F' n (t⁻¹ * u))
      rwa [hcfix] at this
    have h4 := h3.map (galAct F F' n t)
    have e : galAct F F' n t (galAct F F' n (t⁻¹ * u) ε) = galAct F F' n u ε := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    rwa [e] at h4
  have hYcomm : ∀ δ : GL (Fin n) F', nrm s δ = c → Commute δ c := by
    intro δ h
    have := hcomm δ
    rw [h, hcfix] at this
    exact this
  have eY : {δ : GL (Fin n) F' // nrm s δ = c} ≃
      {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} :=
    { toFun := fun δ => ⟨δ₀⁻¹ * δ.1, (memB _).2 (hδ₀c.inv_left.mul_left (hYcomm _ δ.2)), by
          have := key (δ₀⁻¹ * δ.1) (hδ₀c.inv_left.mul_left (hYcomm _ δ.2))
          rw [mul_inv_cancel_left, δ.2] at this
          simpa using this.symm⟩
      invFun := fun ε => ⟨δ₀ * ε.1, by rw [key _ ((memB _).1 ε.2.1), ε.2.2, mul_one]⟩
      left_inv := fun δ => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun ε => Subtype.ext (inv_mul_cancel_left _ _) }
  have eC' : {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} ≃ {x : GL (Fin n) F' // Commute x c} :=
    Equiv.subtypeEquivRight memB
  have eC : {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} ≃
      {x : GL (Fin n) F // Commute x γ} :=
    Equiv.subtypeEquivRight fun x => by
      rw [memB]
      exact ⟨fun h => hinj (by simpa only [map_mul] using h.eq), fun h => h.map _⟩
  rw [Nat.card_congr eY, ← Nat.card_congr eC, ← Nat.card_congr eC']
  exact h90

end Centraliser

theorem card_isNorm_mul_card : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F),
    Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) =
      Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  intro F F' _ _ _ _ s hs n γ
  have hX : Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} =
      Nat.card {g' : GL (Fin n) F' // IsConj (incl F F' n γ) g'} *
        Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} :=
    card_isConj_nrm s hs (incl F F' n γ)
  have hY := card_nrm_eq_mul_card_commute s hs n γ
  have h1 := card_conj_mul_card_commute (incl F F' n γ)
  have h2 := card_conj_mul_card_commute γ
  rw [hX, ← h2, ← h1, ← hY]
  ring

end GlobalTheory.Shin.NormFibre
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.additive_bijective_relation_rowVec_eq_matrix : ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x, ∃ y, R x y) → (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) → (∀ x y, R x y → (x = 0 ↔ y = 0)) → ∃ A : GL (Fin 2) (ZMod N), ∀ x, R x (vmul x A) := by
  first | exact @GlobalTheory.RelLin.main | exact GlobalTheory.RelLin.main | (intros; apply GlobalTheory.RelLin.main <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

theorem _root_.GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧ (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  first | exact @GlobalTheory.WpFam.qAll_isAlgebraic_torsion | exact GlobalTheory.WpFam.qAll_isAlgebraic_torsion | (intros; apply GlobalTheory.WpFam.qAll_isAlgebraic_torsion <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem val_le_exp_of_ord (v : Place k F) (x : F) (d : ℤ) (hd : 0 ≤ d) (h : -d ≤ ord v x) :
    v.1 x ≤ WithZero.exp d := by
  by_cases hx : v.1 x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    unfold ord at h; omega

theorem val_algebraMap_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem val_comb_le (v : Place k F) {m : ℕ} (f : Fin m → F) (c : Fin m → k)
    (B : WithZero (Multiplicative ℤ)) (h : ∀ j, v.1 (f j) ≤ B) : v.1 (∑ j, c j • f j) ≤ B := by
  apply v.1.map_sum_le
  intro j _
  rw [Algebra.smul_def, map_mul]
  calc v.1 (algebraMap k F (c j)) * v.1 (f j) ≤ 1 * B := mul_le_mul' (val_algebraMap_le_one v _) (h j)
    _ = B := one_mul B

theorem val_mulVec_le_one (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j, v.1 (M i j) ≤ 1) (p : Fin n → F) (hp : ∀ i, v.1 (p i) ≤ 1) (i : Fin n) :
    v.1 (M.mulVec p i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply v.1.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (M i j) * v.1 (p j) ≤ 1 * 1 := mul_le_mul' (hM i j) (hp j)
    _ = 1 := one_mul 1

theorem exists_exp_bound (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ d : ℕ, ∀ i j, v.1 (M i j) ≤ WithZero.exp (d : ℤ) := by
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat,
    fun i j => ?_⟩
  by_cases hx : v.1 (M i j) = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    have := Finset.le_sup (f := fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat)
      (Finset.mem_univ (i, j))
    simp only at this
    omega

theorem exists_section_of_large_deg : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.riemann_inequality_cofinal_functionField k F hFF
  refine ⟨γ, fun n g hg hdeg => ?_⟩
  classical
  set B := hg.2.toFinset with hBdef
  choose d0 hd0 using fun v => exists_exp_bound v (g v)⁻¹
  let D : Place k F →₀ ℤ := Finsupp.onFinset B (fun v => if v ∈ B then (d0 v : ℤ) else 0)
    (by intro v hv; by_contra h; exact hv (if_neg h))
  obtain ⟨D', hDD', m, f, hf, hm, hford⟩ := hγ D
  have hD0 : ∀ v, 0 ≤ D' v := fun v => le_trans
    (by simp only [D, Finsupp.onFinset_apply]; split_ifs <;> omega) (hDD' v)
  have hloc : ∀ v, ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)),
      (N : ℤ) = n * ((D' v).toNat : ℕ) - ord v (g v).det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ)) → φ p = 0 →
        ∀ i, v.1 ((g v).mulVec p i) ≤ 1 := by
    intro v
    refine GlobalTheory.T.functionFieldPlace_localIndex_scaled_uniformiser k F hFF v n (g v) _ (hg.1 v) ?_
    intro i j
    by_cases hv : v ∈ B
    · have hDv : D v = d0 v := by simp [D, Finsupp.onFinset_apply, hv]
      calc v.1 ((g v)⁻¹ i j) ≤ WithZero.exp (d0 v : ℤ) := hd0 v i j
        _ ≤ _ := by
          rw [WithZero.exp_le_exp]; have := hDD' v; rw [hDv] at this; omega
    · have hU : Unimod v (g v) := by simpa [B] using hv
      have hU' := ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.2 n (g v) (g v) hU hU).2
      calc v.1 ((g v)⁻¹ i j) ≤ 1 := hU'.1 i j
        _ = WithZero.exp 0 := rfl
        _ ≤ _ := by rw [WithZero.exp_le_exp]; omega
  choose N φ hN hφ using hloc
  set S := B ∪ D'.support with hS
  have hsumD : D'.sum (fun _ m => m) = ∑ v ∈ S, D' v := by
    unfold Finsupp.sum
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv; simpa using hv
  have hdegS : deg g = ∑ v ∈ S, ord v (g v).det := by
    unfold deg
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Finset.coe_union]; left
    simp only [B, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hU; apply hv
    simp [ord, hU.2]
  have hNsum : ((∑ v ∈ S, N v : ℕ) : ℤ) < n * m := by
    push_cast
    rw [Finset.sum_congr rfl (fun v _ => hN v), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : ∀ v, (((D' v).toNat : ℕ) : ℤ) = D' v := fun v => Int.toNat_of_nonneg (hD0 v)
    simp_rw [this]
    rw [← hsumD, ← hdegS]
    have := mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg n)
    nlinarith
  obtain ⟨c, hp0, hpψ⟩ := GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel k F (Place k F) n m f hf S N φ (by exact_mod_cast hNsum)
  refine ⟨_, hp0, fun v i => ?_⟩
  have hpb : ∀ i, v.1 (∑ j, c i j • f j) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ) := fun i =>
    val_comb_le v f (c i) _ (fun j => val_le_exp_of_ord v _ _ (by omega)
      (by rw [Int.toNat_of_nonneg (hD0 v)]; exact hford j v))
  by_cases hv : v ∈ S
  · exact hφ v _ hpb (hpψ v hv) i
  · have hvB : v ∉ B := fun h => hv (Finset.mem_union_left _ h)
    have hD'v : D' v = 0 := by
      by_contra h; exact hv (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h))
    have hU : Unimod v (g v) := by simpa [B] using hvB
    apply val_mulVec_le_one v _ hU.1
    intro i; have := hpb i; rw [hD'v] at this; simpa using this

end GlobalTheory.Nef
end
end
