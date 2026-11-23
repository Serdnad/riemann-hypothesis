module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerRowOperatorMemDualWeylEndSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGaussFactorisationCoeffSmulInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle927
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory.HTSummand



theorem summand_of_liftedCoords : ∀ {C : Type} [CommRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F →
  ∀ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) →
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) →
    (∀ k, y k ∈ LinearMap.range π) → (∀ j k, ℓ j (y k) = if j = k then 1 else 0) →
  ∃ G₀ M₀ : Submodule C H, G₀ ⊓ M₀ = ⊥ ∧ G₀ ⊔ M₀ = LinearMap.range π ∧ (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) ∧
    G₀ ⊔ I • LinearMap.range π = F ⊓ LinearMap.range π ∧
    ∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀ := by
  intro C _ I hI A _ H _ _ σ hproj a χ π hπ hσπ F hIF n κ ℓ y hℓ hF hy hδ
  have hl : ∀ k, ∃ l : H →ₗ[C] C, (∀ c x, l (σ c x) = χ (κ k) c * l x) ∧
      ∀ x, Ideal.Quotient.mk I (l x) = ℓ k x :=
    fun k => GlobalTheory.T.exists_equivariantLift_functional_quotient_projective I σ hproj (χ (κ k)) (ℓ k) (hℓ k)
  choose l hlσ hlℓ using hl
  have hII : ∀ u v : C, u ∈ I → v ∈ I → u * v = 0 := by
    intro u v hu hv
    have h := Ideal.mul_mem_mul hu hv
    rw [← sq, hI] at h
    simpa using h
  have hσQ : ∀ c, ∀ x ∈ LinearMap.range π, σ c x ∈ LinearMap.range π := by
    rintro c _ ⟨z, rfl⟩
    refine ⟨σ c z, ?_⟩
    show (π * σ c) z = (σ c * π) z
    rw [hσπ]
  let e : Fin n → Fin n → C := fun j m => l j (y m) - if j = m then 1 else 0
  have he : ∀ j m, e j m ∈ I := by
    intro j m
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [e, map_sub, hlℓ, hδ]
    split_ifs <;> simp
  let x : Fin n → H := fun k => y k - ∑ m, e m k • y m
  have hxQ : ∀ k, x k ∈ LinearMap.range π := fun k =>
    Submodule.sub_mem _ (hy k) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hy m))
  have hlx : ∀ j k, l j (x k) = if j = k then 1 else 0 := by
    intro j k
    have h1 : ∀ m, e m k * l j (y m) = if j = m then e m k else 0 := by
      intro m
      have h0 := hII _ _ (he m k) (he j m)
      rw [show l j (y m) = e j m + (if j = m then 1 else 0) by simp [e], mul_add, h0]
      split_ifs <;> simp

    simp only [x, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_ite_eq]
    simp [e]
  let G₀ : Submodule C H := LinearMap.range π ⊓ ⨅ k, LinearMap.ker (l k)
  have hG : ∀ z, z ∈ G₀ ↔ z ∈ LinearMap.range π ∧ ∀ k, l k z = 0 := by
    intro z
    simp only [G₀, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  have key : ∀ q ∈ LinearMap.range π, q - ∑ k, l k q • x k ∈ G₀ := by
    intro q hq
    refine (hG _).2 ⟨Submodule.sub_mem _ hq (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (hxQ k)), fun j => ?_⟩

    simp [map_sum, hlx]
  refine ⟨G₀, Submodule.span C (Set.range x), ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro z ⟨hzG, hzM⟩
    rw [Submodule.mem_bot]
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hzM
    have hc : ∀ j, c j = 0 := fun j => by
      have h := ((hG _).1 hzG).2 j

      simpa [map_sum, hlx] using h
    simp [hc]
  · refine le_antisymm (sup_le inf_le_left
      (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hxQ k))) ?_
    intro q hq
    rw [← sub_add_cancel q (∑ k, l k q • x k)]
    exact Submodule.add_mem_sup (key q hq) (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · intro c z hz
    rw [hG] at hz ⊢
    exact ⟨hσQ c z hz.1, fun k => by rw [hlσ, hz.2, mul_zero]⟩
  · apply le_antisymm
    · refine sup_le ?_ (le_inf ((Submodule.smul_mono le_rfl le_top).trans hIF)
        Submodule.smul_le_right)
      intro z hz
      rw [hG] at hz
      exact ⟨(hF z hz.1).2 (fun k => by rw [← hlℓ, hz.2 k, map_zero]), hz.1⟩
    · rintro z ⟨hzF, hzQ⟩
      have hlI : ∀ k, l k z ∈ I := fun k => by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hlℓ]
        exact (hF z hzQ).1 hzF k
      rw [← sub_add_cancel z (∑ k, l k z • x k)]
      exact Submodule.add_mem_sup (key z hzQ) (Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem_smul (hlI k) (hxQ k))
  · intro d hd
    have hv : ∀ c k, σ c (x k) - χ (κ k) c • x k ∈ G₀ := by
      intro c k
      refine (hG _).2 ⟨Submodule.sub_mem _ (hσQ c _ (hxQ k)) (Submodule.smul_mem _ _ (hxQ k)),
        fun j => ?_⟩
      rw [map_sub, hlσ, map_smul, hlx, smul_eq_mul]
      split_ifs with h
      · subst h; ring
      · simp
    refine ⟨fun i => ∑ k ∈ Finset.univ.filter (fun k => κ k = i), l k d • x k, ?_, ?_⟩
    · intro i c

      simp only [map_sum, map_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Submodule.sum_mem
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [← hk.2, smul_comm, ← smul_sub]
      exact Submodule.smul_mem _ _ (hv c k)
    · rw [Finset.sum_fiberwise]
      exact key d hd

end GlobalTheory.HTSummand
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_eq_eval_genericRowSubstitution : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O), rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := by
  first | exact @GlobalTheory.GenCoef.RowSubstSum.main | exact GlobalTheory.GenCoef.RowSubstSum.main | (intros; apply GlobalTheory.GenCoef.RowSubstSum.main <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_diagonal_eq_sum_components : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)), (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := by
  first | exact @GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components | exact GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components | (intros; apply GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_transvection_eq_sum : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.transvection a b r) f = ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := by
  first | exact @GlobalTheory.RowSubstTransvection.rowSubst_transvection | exact GlobalTheory.RowSubstTransvection.rowSubst_transvection | (intros; apply GlobalTheory.RowSubstTransvection.rowSubst_transvection <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.rowSubstDualWeylExpressible_matrix_mul_closed : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y Y' : Matrix (Fin N) (Fin N) R), Expr O N ν R Y → Expr O N ν R Y' → Expr O N ν R (Y * Y') := by
  first | exact @GlobalTheory.GenCoef.expr_mul | exact GlobalTheory.GenCoef.expr_mul | (intros; apply GlobalTheory.GenCoef.expr_mul <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.dividedPowerRowOperator_mem_dualWeylEndSubalgebra : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N), a ≠ b → ∀ k : ℕ, ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν, (p f : MvPolynomial (Fin N × Fin N) O) = rowDiv O a b k (f : MvPolynomial (Fin N × Fin N) O) := by
  first | exact @GlobalTheory.GenCoef.rowDiv_mem_dwAlg | exact GlobalTheory.GenCoef.rowDiv_mem_dwAlg | (intros; apply GlobalTheory.GenCoef.rowDiv_mem_dwAlg <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.genericGaussFactorisation_coeff_smul_injective : ∀ (O : Type) [CommRing O] (N : ℕ) (M : Type) [AddCommGroup M] [Module O M] (s : Finset (Fin N × Fin N →₀ ℕ)) (c : (Fin N × Fin N →₀ ℕ) → M), (∀ n, ∑ m ∈ s, (lduHom O N (monomial m 1)).coeff n • c m = 0) → ∀ m ∈ s, c m = 0 := by
  first | exact @GlobalTheory.GenCoef.lduHom_coeff_smul_injective | exact GlobalTheory.GenCoef.lduHom_coeff_smul_injective | (intros; apply GlobalTheory.GenCoef.lduHom_coeff_smul_injective <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem rigToLie_toBase_rig {p : ℕ} [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [Field k']
    [CharP k' p] [Algebra k k'] (G : PDivGroup p k) (r : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (w : G.dual.omega) :
    (G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig r)
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom ((G.dual.toBase k').omega w)) =
      algebraMap k k' (G.rigToLie (p_eq_zero p k) r w) := by
  set_option backward.isDefEq.respectTransparency false in
   change (G.baseChange k').primLie ((G.baseChange k').extChar (p_eq_zero p k')
    ((G.baseChange k').rigToExt ((G.toBase k').rig r))) _ =
    algebraMap k k' (G.primLie (G.extChar (p_eq_zero p k) (G.rigToExt r)) w)
  set_option backward.isDefEq.respectTransparency false in
   rw [SemiHom.rigToExt_rig, SemiHom.extChar_vecExt _ (p_eq_zero p k)]
  exact primLie_toBase G _ w

theorem linearMap_eq_of_liftSemi_surjective {R R' M N : Type} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N]
    (f : M →ₛₗ[algebraMap R R'] N) (hf : Function.Surjective (liftSemi f)) (F₁ F₂ : N →ₗ[R'] R')
    (h : ∀ m, F₁ (f m) = F₂ (f m)) : F₁ = F₂ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨t, rfl⟩ := hf v
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r m => rw [liftSemi_tmul, map_smul, map_smul, h]


theorem red_of_isTr (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type)
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k) (h' : G'.IsEt) (h : G.IsEt)
    (s : SemiHom σ G' G) (l : Mod B G h) (l' : Mod B G' h') (hT : IsTr B σ h' h s l l') :
    red B G' h' l' = s.rig (red B G h l) := by
  letI : Algebra k k' := σ.toAlgebra
  obtain ⟨hb, lb, h1, h2⟩ := hT
  haveI := B.free _ hb
  haveI := B.finite _ hb
  obtain ⟨r', hr', -, -⟩ := wittDual_reduction p k' _ _ (B.red _ hb) (B.red_surjective _ hb)
    (B.red_eq_zero _ hb)
  have hψ : ∀ m, r' lb (B.red _ hb m) = WittVector.constantCoeff (lb m) := hr' lb
  have key1 : ∀ w : G.dual.omega,
      r' lb ((G.dual.baseChange k').rigOfOmega ((G.dual.toBase k').omega w)) =
        σ (G.rigToLie (p_eq_zero p k) (red B G h l) w) := by
    intro w
    obtain ⟨x, hx⟩ := B.red_surjective _ (dual_conn h) (G.dual.rigOfOmega w)
    have e1 : (G.dual.baseChange k').rigOfOmega ((G.dual.toBase k').omega w) =
        B.red _ hb (B.smap hb (dual_conn h) (G.dual.toBase k') x) := by
      rw [B.red_smap, hx, SemiHom.rig_rigOfOmega]
    have e2 : G.rigToLie (p_eq_zero p k) (red B G h l) w = WittVector.constantCoeff (l x) := by
      rw [rigToLie_red, LinearMap.dualMap_apply, ← hx]
      exact (redDual_spec B G h).1 l x
    have e3 : WittVector.constantCoeff (WittVector.map σ (l x)) = σ (WittVector.constantCoeff (l x)) := by
      simp [WittVector.constantCoeff_apply, WittVector.map_coeff]
    exact (congrArg (r' lb) e1).trans ((hψ _).trans ((congrArg _ (h1 x)).trans (e3.trans (congrArg σ e2.symm))))
  have key2 : ((G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig (red B G h l))).comp
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom) =
      (r' lb).comp (G.dual.baseChange k').rigOfOmega :=
    linearMap_eq_of_liftSemi_surjective (G.dual.toBase k').omega
      (T.omega_baseChange_bijective_of_p_eq_zero G.dual k' (p_eq_zero p k)).2 _ _ fun w => by
        set_option backward.isDefEq.respectTransparency false in
          simp only [LinearMap.comp_apply]
          rw [rigToLie_toBase_rig]
          exact (key1 w).symm
  have hinj := (PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k'
    (p_eq_zero p k') G' h').1.1
  apply hinj
  rw [rigToLie_red]
  refine LinearMap.ext fun w' => ?_
  rw [LinearMap.dualMap_apply]
  obtain ⟨x', hx'⟩ := B.red_surjective _ (dual_conn h') (G'.dual.rigOfOmega w')
  have hs : ∀ n a, s.app n a = (SemiHom.ofHom s.lift).app n ((G.toBase k').app n a) := fun n a => by
    rw [SemiHom.ofHom_app, toBase_app, SemiHom.lift_app, one_smul]
  have e4 : B.red _ hb (B.map hb (dual_conn h')
      ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) x') =
      (G.dual.baseChange k').rigOfOmega (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv
        (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w')) := by
    change B.red _ hb (B.smap hb (dual_conn h') (SemiHom.ofHom _) x') = _
    rw [B.red_smap, hx', SemiHom.rig_rigOfOmega, SemiHom.ofHom_omega, omegaMap_comp,
      LinearMap.comp_apply]
  have e5 : G'.rigToLie (p_eq_zero p k') (s.rig (red B G h l)) w' =
      (G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig (red B G h l))
        (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w') := by
    rw [← (G.toBase k').rig_rig (SemiHom.ofHom s.lift) s hs, SemiHom.ofHom_rig,
      rigToLie_rigExtMap, lieMap_apply]
  have e6 : ∀ v, omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv v) = v := fun v => by
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply]
  rw [← hx', (redDual_spec B G' h').1, h2, ← hψ, e4, e5]
  have e7 := LinearMap.congr_fun key2 (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv
    (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w'))
  simp only [LinearMap.comp_apply, e6] at e7
  exact e7.symm

end GlobalTheory.Dieu.EtFromConn
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem isTr_ofHom : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H) (l : Mod B H hH), IsTr B (RingHom.id k) hG hH (SemiHom.ofHom f) l (l ∘ₗ B.map (dual_conn hH) (dual_conn hG) (dualHom G H f)) := by
  intro p _ B k _ _ _ G H hG hH f l
  unfold IsTr
  letI : Algebra k k := (RingHom.id k).toAlgebra
  have hd := dual_conn hH
  have hd' := dual_conn hG
  have hb : (H.dual.baseChange k).IsConn := (baseChange_isConn_isEt p k k H.dual).1 hd
  let φ : H.dual ⟶ H.dual.baseChange k := SemiHom.lift (SemiHom.ofHom (𝟙 H.dual))
  have hφ : ∀ x, B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd (H.dual.toBase k) x) = x := by
    intro x
    rw [← B.smap_comp hd hb hd (H.dual.toBase k) (SemiHom.ofHom φ) (SemiHom.ofHom (𝟙 _)), B.smap_id]
    intro n a
    exact ((SemiHom.lift_app _ n 1 a).trans (one_smul _ _)).symm
  refine ⟨hb, l ∘ₗ B.map hd hb φ, fun x => ?_, fun y => ?_⟩
  · change l (B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd (H.dual.toBase k) x)) = _
    rw [hφ, WittVector.map_id, RingHom.id_apply]
  · have hc : ∀ n a, (SemiHom.ofHom ((PerfdLat.dualBaseChange k H).inv ≫
        dualHom G (H.baseChange k) (SemiHom.ofHom f).lift)).app n a =
        (H.dual.toBase k).app n ((SemiHom.ofHom (dualHom G H f)).app n a) := by
      intro n a
      change (CartierDual.baseChange k k (H.A n)).symm (CartierDual.map ((SemiHom.ofHom f).lift.app n) a) = (1 : k) ⊗ₜ CartierDual.map (f.app n) a
      apply EquivLike.injective (CartierDual.baseChange k k (H.A n))
      rw [BialgEquiv.apply_symm_apply]
      refine WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun b m => ?_)
      simp
      rw [SemiHom.lift_app, SemiHom.ofHom_app, map_smul, smul_eq_mul, mul_comm]
    have key := B.smap_comp hb hd hd' (SemiHom.ofHom (dualHom G H f)) (H.dual.toBase k) _ hc y
    change l (B.map hd hd' (dualHom G H f) y) = l (B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd' _ y))
    rw [key, hφ]
    rfl

end GlobalTheory.Dieu.EtFromConn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem comp_one₂ {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

theorem pullUnivP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)) (AE : Over Y.left) [GrpObj AE] (φE : AE.left ⟶ AH.left) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE → (∀ y, (ηE y).left ≫ φE = (u y).left) → (∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) → (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) → ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x) → ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ Y.left, z ≫ Y.hom = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D N H AH _ actH Y u AE _ φE ηE hE hηu huniv T g AT _ φ act eta hT hact heta
  let Tg : Over H := Over.mk g
  let e : Tg ⟶ Over.mk ((𝟙_ (Over T)).hom ≫ g) := Over.homMk (𝟙 T) (by simp [Tg])
  let u' : D.La → (Tg ⟶ AH) := fun x => e ≫ pushHom hT (𝟙_ (Over T)) (eta x)
  have hu'l : ∀ x, (u' x).left = (eta x).left ≫ φ := fun x => by
    show 𝟙 T ≫ (eta x).left ≫ φ = _
    rw [Category.id_comp]
  have hadd : ∀ x y, u' (x + y) = u' x * u' y := fun x y => by
    show e ≫ pushHom hT _ (eta (x + y)) = (e ≫ pushHom hT _ (eta x)) * (e ≫ pushHom hT _ (eta y))
    rw [heta.1, map_mul, MonObj.comp_mul]
  have hlin : ∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c := fun c x => by
    apply Over.OverMorphism.ext
    show (u' (c • x)).left = (u' x ≫ actH.act c).left
    rw [hu'l, Over.comp_left, hu'l, heta.2.1, Over.comp_left, Category.assoc, hact, Category.assoc]
  have hker : ∀ x, u' (N • x) = 1 := fun x => by
    show e ≫ pushHom hT _ (eta (N • x)) = 1
    rw [heta.2.2, map_one, comp_one₂]
  obtain ⟨h, hh, hun⟩ := huniv Tg u' hadd hlin hker
  have hz : h.left ≫ Y.hom = g := Over.w h
  have hw : φ ≫ AH.hom = (AT.hom ≫ h.left) ≫ Y.hom := by rw [hT.1.w, Category.assoc, hz]
  let ψ : AT.left ⟶ AE.left := hE.1.lift φ (AT.hom ≫ h.left) hw
  have hψ₁ : ψ ≫ φE = φ := hE.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ AE.hom = AT.hom ≫ h.left := hE.1.lift_snd _ _ _
  have hhl : ∀ y, h.left ≫ (u y).left = (eta y).left ≫ φ := fun y => by
    rw [← Over.comp_left, hh y, hu'l]
  refine ⟨h.left, ⟨hz, ψ, ?_, hψ₁, fun y => ?_⟩, ?_⟩
  · exact IsGrpPullback.cancel hE (hT.congr hz.symm hψ₁.symm) hψ₂
  · apply hE.1.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, hηu, hhl]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (eta y), Category.assoc, Over.w (ηE y)]
      rfl
  · rintro z₂ ⟨hz₂, ψ₂, -, hψ₂₁, he₂⟩
    let h₂ : Tg ⟶ Y := Over.homMk z₂ hz₂
    have : h₂ = h := hun h₂ fun x => by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hu'l]
      show z₂ ≫ (u x).left = _
      rw [← hηu, ← Category.assoc, ← he₂, Category.assoc, hψ₂₁]
    exact congrArg (fun k => k.left) this

end GlobalTheory.UPel.HT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.EndLoc.HomGlue

theorem Pt.comp_f_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z W : Scheme.{0}} {x x' : Pt A B L M Z} (e : x = x') (p : W ⟶ pullback A.hom x.t)
    (q : W ⟶ pullback A.hom x'.t) (h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _)
    (h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _) : p ≫ x.f = q ≫ x'.f := by
  subst e
  obtain rfl : p = q := pullback.hom_ext h1 h2
  rfl

theorem Pt.ext_cover : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (y y' : HomGlue.Pt A B L M Z),
    (∀ i, y.map hL hM (𝒰.f i) = y'.map hL hM (𝒰.f i)) → y = y' := by
  intro S A B _ _ L M hL hM Z 𝒰 y y' h
  have ht : y.t = y'.t := 𝒰.hom_ext _ _ fun i => congrArg Pt.t (h i)
  obtain ⟨t, f, w⟩ := y
  obtain ⟨t', f', w'⟩ := y'
  dsimp only at ht
  subst ht
  suffices hf : f = f' by subst hf; rfl
  refine (Scheme.Pullback.openCoverOfRight 𝒰 A.hom t).hom_ext _ _ fun (i : 𝒰.I₀) => ?_
  have := Pt.comp_f_eq (h i) (𝟙 _) (𝟙 _) rfl rfl
  change 𝟙 _ ≫ pmap A t (𝒰.f i) ≫ f = 𝟙 _ ≫ pmap A t (𝒰.f i) ≫ f' at this
  rw [Category.id_comp, Category.id_comp] at this
  have e : (Scheme.Pullback.openCoverOfRight 𝒰 A.hom t).f i = pmap A t (𝒰.f i) := by
    rw [Scheme.Pullback.openCoverOfRight_f]
    apply pullback.hom_ext
    · erw [pullback.lift_fst]
    · erw [pullback.lift_snd]
  rw [e]
  exact this

end GlobalTheory.EndLoc.HomGlue
end

section

open GlobalTheory

theorem _root_.GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung'
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.range (PDivGroup.frobTwist h G).rigOfOmega ≤
      LinearMap.range (PDivGroup.rigExtMap (PDivGroup.verschiebung h G)) :=
  PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung p K h G
end
