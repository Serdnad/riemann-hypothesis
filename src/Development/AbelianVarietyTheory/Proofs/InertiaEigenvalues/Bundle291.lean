module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.decompletion_frame_of_matrix_form : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsActC act → IsGen χ K m g → (∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m)) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ) → (∀ i j, ‖D i j‖ ≤ 1) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ ≤ 1) ∧ D * X = (l : PadicComplex l) • (1 : Matrix (Fin d) (Fin d) (PadicComplex l))) → (∀ σ ∈ Gj K m, ∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, X i j ∈ intC (Ks K m)) ∧ M σ * D.map (act σ) = D * X) → (∀ σ ∈ Hinf K, M σ * D.map (act σ) = D) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ < rho1 l) ∧ M g * D.map (act g) - D = D * X) → ∃ U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l), IsDec act χ K m M D U g := by
  first | exact @GlobalTheory.Cyc.Decomp.isDec_of_matrix | exact GlobalTheory.Cyc.Decomp.isDec_of_matrix | (intros; apply GlobalTheory.Cyc.Decomp.isDec_of_matrix <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem unr_of_finite_inertia : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (ρ '' (IK K : Set ↥(GK K))).Finite →
    ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1), (∀ g ∈ IK K', ρ ⟨g, GK_le hK g.2⟩ = 1) ∧
      ∀ (g : ↥(GK K')) i j, ‖(((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) -
        (1 : Matrix n n (Om l)) i j‖ < 1 := by
  intro l _ n _ _ K r ρ hρ hfin
  let F : ↥(GK K) → (n → n → Om l) := fun g i j => (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)
  have hF : Continuous F := continuous_pi fun i => continuous_pi fun j => hρ.cont i j
  let cm : GL n ↥(MaximalUnramifiedExtension l) → (n → n → Om l) := fun M i j => (((M : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)
  have hcm : Function.Injective cm := by
    intro M M' h
    ext i j
    exact congrFun (congrFun h i) j
  have hone : ∀ i j, (((1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) = (1 : Matrix n n (Om l)) i j := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  let T : Set (n → n → Om l) := cm '' (ρ '' (IK K : Set ↥(GK K)) \ {1})
  have hT : T.Finite := (hfin.sdiff).image cm
  let V : Set (n → n → Om l) := {x | ∀ i j, ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} ∩ Tᶜ
  have hV : IsOpen V := by
    refine IsOpen.inter ?_ hT.isClosed.isOpen_compl
    have : {x : n → n → Om l | ∀ i j, ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} =
        ⋂ i, ⋂ j, {x : n → n → Om l | ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} := by
      ext
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (by fun_prop) continuous_const
  have h1V : F 1 ∈ V := by
    refine ⟨fun i j => ?_, ?_⟩
    · show ‖(((ρ 1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) - (1 : Matrix n n (Om l)) i j‖ < 1
      rw [map_one, Units.val_one, hone, sub_self, norm_zero]
      exact one_pos
    · rintro ⟨M, hM, hMF⟩
      have hM1 : M = ρ 1 := hcm hMF
      exact hM.2 (by rw [hM1, map_one]; rfl)
  have hU : IsOpen (F ⁻¹' V) := hV.preimage hF
  obtain ⟨U', hU', hUe'⟩ := isOpen_induced_iff.1 hU
  have h1' : (1 : GQ l) ∈ U' := by
    have : (1 : ↥(GK K)) ∈ Subtype.val ⁻¹' U' := by
      rw [hUe']
      exact h1V
    exact this
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) U').1 (hU'.mem_nhds h1')
  refine ⟨supExt K ⟨E, hE⟩, le_sup_left, ?_⟩
  have key : ∀ g : ↥(GK (supExt K ⟨E, hE⟩)),
      F ⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ ∈ V := by
    intro g
    have : (⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ : ↥(GK K)) ∈ Subtype.val ⁻¹' U' :=
      hEU (GK_le (K := ⟨E, hE⟩) (K' := supExt K ⟨E, hE⟩) le_sup_right g.2)
    rw [hUe'] at this
    exact this
  refine ⟨fun g hg => ?_, fun g i j => (key g).1 i j⟩
  have hin : (⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ : ↥(GK K)) ∈ IK K := by
    have hmap : (IK (supExt K ⟨E, hE⟩)).map (Subgroup.inclusion (GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left)) ≤
        IK K := by
      unfold IK
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨σ, hσ, rfl⟩
      intro x hx
      exact hσ x hx
    exact hmap ⟨g, hg, rfl⟩
  by_contra hne
  exact (key g).2 ⟨_, ⟨⟨_, hin, rfl⟩, hne⟩, rfl⟩

end GlobalTheory.PMon
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Inhab

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

include P in
theorem fixed_frob (c : ↥(MaximalUnramifiedExtension l)) (hc : frobUr (l := l) c = c) : ∃ q : ℚ_[l], algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q = c := by
  let K := adjExt (c : Om l)
  let x : ↥(K0 K) := ⟨c, mem_adjExt _, c.2⟩
  have h1 : (P.PD K).φ (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := by
    rw [P.PD_φ, phiB_algebraMap, hc]
  have h2 : (P.PD K).ι (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) ∈ (P.PD K).Fil 0 := by
    have e : (P.PD K).ι (algebraMap ↥(K0 K) P.R.B x) = algebraMap ↥(K0 K) P.R.BdR x := (P.PD K).ι.commutes x
    have e2 : algebraMap ↥(K0 K) P.R.BdR x = (algebraMap ↥(K0 K) ↥K.1 x) • (1 : P.R.BdR) := by
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, Algebra.algebraMap_eq_smul_one]
    have e3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c = algebraMap ↥(K0 K) P.R.B x := rfl
    rw [e3, e, e2]
    exact Submodule.smul_mem _ _ (P.PD K).one_mem
  obtain ⟨q, hq⟩ := (P.PD K).fund _ h1 h2
  haveI := nontrivial_B P
  refine ⟨q, (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective ?_⟩
  rw [← hq, ← IsScalarTower.algebraMap_apply]

theorem kd_alg (q : ℚ_[l]) : kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]; rfl

theorem act_zpow (g : GQ l) (a : ℤ) :
    P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
      algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    ext; simp [localPrime_galoisAction_periodT, Algebra.smul_def]
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at h2
  rw [← map_zpow P.χQ]
  exact h2

end GlobalTheory.PMon.Inhab

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

variable {l : ℕ} [Fact l.Prime] {r : ℕ}

def frobMat (ω : Fin r → ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.of fun m k => fr l m (ω k)

def resMat (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) :
    Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (frobMat ω)

theorem resMat_apply (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (a b : n × Fin r) :
    resMat n ω a b = if a.1 = b.1 then fr l a.2 (ω b.2) else 0 := by
  simp [resMat, frobMat, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem isUnit_det_resMat (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) : IsUnit (resMat n ω).det := by
  rw [resMat, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul]
  exact (isUnit_iff_ne_zero.2 hdet).pow _

def resGL (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) :
    GL (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
  Matrix.GeneralLinearGroup.mk'' (resMat n ω) (isUnit_det_resMat n ω hdet)

def blockGL {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (U : Fin r → GL n R) :
    GL (n × Fin r) R where
  val := Matrix.blockDiagonal fun m => (U m : Matrix n n R)
  inv := Matrix.blockDiagonal fun m => (((U m)⁻¹ : GL n R) : Matrix n n R)
  val_inv := by rw [← Matrix.blockDiagonal_mul]; simp only [Units.mul_inv]; exact Matrix.blockDiagonal_one
  inv_val := by rw [← Matrix.blockDiagonal_mul]; simp only [Units.inv_mul]; exact Matrix.blockDiagonal_one

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def U0 (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (U : Fin r → GL n P.R.BdR) : GL (n × Fin r) P.R.BdR :=
  (Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+* Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom
    (resGL n ω hdet))⁻¹ * blockGL U

def Ymat (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (A₀ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B :=
  (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B)

def colv (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (A₀ : GL (n × Fin r) P.R.B) (c : n × Fin r) (i : n) : P.R.B :=
  ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c

def LatC (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) : Prop :=
  (∀ i, P.φB^[r] (a i) = a i) ∧ ∀ m : Fin r, ∃ w : n → P.R.BdR, (∀ i, w i ∈ Fil P 0) ∧
    (fun i => ev P m (a i)) = ((U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => tz P (eps x y (m, j))).mulVec w

end GlobalTheory.PMon.ResR

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CountL

theorem length_le_of_semilinear {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (hf : Function.Injective f) : Module.length R M ≤ Module.length S N := by
  have : RingHomSurjective σ := ⟨hσ⟩
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_strictMono (Submodule.map f) (Submodule.map_strictMono_of_injective hf)

theorem length_le_inf_comap_add {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (C : Submodule R M) (A H : Submodule S N) (hC : ∀ x ∈ C, f x ∈ A) :
    Module.length R ↥C ≤
      Module.length R ↥(C ⊓ H.comap f) + Module.length S (↥A ⧸ H.comap A.subtype) := by
  let g : ↥C →ₛₗ[σ] (↥A ⧸ H.comap A.subtype) :=
    (H.comap A.subtype).mkQ.comp ((f.domRestrict C).codRestrict A fun x => hC x x.2)
  have hg : ∀ x : ↥C, x ∈ LinearMap.ker g → f x ∈ H := fun x hx =>
    (Submodule.Quotient.mk_eq_zero (H.comap A.subtype)).1 hx
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype (LinearMap.ker g).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)]
  refine add_le_add ?_ ?_
  · refine Module.length_le_of_injective
      ((C.subtype.comp (LinearMap.ker g).subtype).codRestrict (C ⊓ H.comap f)
        fun x => ⟨x.1.2, hg x.1 x.2⟩) ?_
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · refine length_le_of_semilinear hσ ((LinearMap.ker g).liftQ g le_rfl) ?_
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem exists_le_forall_le {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (K : ι → Submodule R M) (C : Submodule R M) (b : ℕ∞)
    (h : ∀ q, ∀ C₀ ≤ C, Module.length R ↥C₀ ≤ Module.length R ↥(C₀ ⊓ K q) + b) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C' ≤ K q) ∧
      Module.length R ↥C ≤ (Q.card : ℕ∞) * b + Module.length R ↥C' := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨C₀, h₁, h₂, h₃⟩ := ih
    refine ⟨C₀ ⊓ K a, inf_le_left.trans h₁, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact inf_le_right
      · exact inf_le_left.trans (h₂ q hq)
    · rw [Finset.card_insert_of_notMem ha]
      refine h₃.trans ((add_le_add le_rfl (h a C₀ h₁)).trans (le_of_eq ?_))
      push_cast
      ring

theorem length_quot_natCast_le {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (p : ℕ) :
    Module.length S (S ⧸ Ideal.span {(p : S)}) ≤ Module.length R (R ⧸ Ideal.span {(p : R)}) := by
  refine length_le_of_semilinear (σ := e.symm.toRingHom) e.symm.surjective
    (Submodule.mapQ (Ideal.span {(p : S)}) (Ideal.span {(p : R)}) e.symm.toRingHom.toSemilinearMap ?_) ?_
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨e.symm y, by
      show _ = e.symm (y * p)
      simp⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : e.symm x ∈ Ideal.span {(p : R)} := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton'.2 ⟨e y, ?_⟩)
    simpa using congrArg e hy

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
noncomputable def locFunS {D : D7} (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    (GE D.nd → KOG (D.nd.O i) k) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) where
  toFun := locFun i M w hw
  map_add' a b := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (e : ℕ), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs M e ∧ ∀ f ∈ C, InCut i r Xs M w hw f) → ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ f ∈ C', IsFinL i M f) ∧ Module.length (D.nd.O i) ↥C ≤ (((placesOver D.host.E (D.nd.l i)).ncard * e : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) + Module.length (D.nd.O i) ↥C' := by
  intro D i r Xs k M C e h
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin := finite_placesOver D.host.E (D.nd.l i) hl.ne_zero
  letI : Fintype ↥(placesOver D.host.E (D.nd.l i)) := hfin.fintype
  obtain ⟨C', h₁, h₂, h₃⟩ := exists_le_forall_le
    (fun q : ↥(placesOver D.host.E (D.nd.l i)) =>
      (HfD (Br.PD D.loc D.nbr i q.1 q.2) (Br.locLat D.nbr i q.1 q.2 M)).comap (locFunS i M q.1 q.2))
    C ((e : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i)) (by
      rintro ⟨w, hw⟩ C₀ hC₀
      refine (length_le_inf_comap_add (D.nbr i w hw).eO.surjective (locFunS i M w hw) C₀
        (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M)) _
        (fun f hf => (h w hw).2 f (hC₀ hf))).trans (add_le_add le_rfl ?_)
      refine le_trans (h w hw).1 (mul_le_mul' le_rfl ?_)
      unfold lenOl lenQ
      rw [Br.PD_p]
      exact length_quot_natCast_le (D.nbr i w hw).eO _) Finset.univ
  refine ⟨C', h₁, fun f hf w hw => h₂ ⟨w, hw⟩ (Finset.mem_univ _) hf, ?_⟩
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← mul_assoc] at h₃
  rw [Nat.cast_mul]
  exact h₃

end GlobalTheory.Cut.CountL
end

section

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp.ParInd

section Blocks
variable {R : Type} [CommRing R] {a b : ℕ}

theorem entN_tl (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin a) :
    entN M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_br (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin b) :
    entN M (a + i) (a + j) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_self {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) : entN M i j = M i j := by
  simp [entN]

theorem det_par (M : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0) :
    M.det = (Matrix.of fun i j : Fin a => entN M i j).det *
      (Matrix.of fun i j : Fin b => entN M (a + i) (a + j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    apply h <;> simp
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, entN_tl, entN_br]

theorem exists_blocks (p : GL (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix _ _ R) i j = 0) :
    ∃ (x : GL (Fin a) R) (y : GL (Fin b) R),
      (∀ i j : Fin a, (x : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) i j) ∧
      (∀ i j : Fin b, (y : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) (a + i) (a + j)) := by
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [det_par _ h] at hu
  have h1 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu)
  have h2 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)
  exact ⟨h1.unit, h2.unit, fun i j => by simp, fun i j => by simp⟩

def dg (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  fun i j => if (i : ℕ) < a ∧ (j : ℕ) < a then entN x i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN y (i - a) (j - a) else 0

theorem dg_par (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin (a + b))
    (hj : (j : ℕ) < a) (hi : a ≤ (i : ℕ)) : dg x y i j = 0 := by
  unfold dg
  rw [if_neg (by omega), if_neg (by omega)]

theorem dg_tl (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    entN (dg x y) i j = x i j := by
  rw [entN_tl]
  simp [dg, entN_self]

theorem dg_br (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    entN (dg x y) (a + i) (a + j) = y i j := by
  rw [entN_br]
  simp [dg, entN_self]

theorem dg_det (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) :
    (dg x y).det = x.det * y.det := by
  rw [det_par _ (dg_par x y)]
  congr 2 <;> ext i j <;> simp [dg_tl, dg_br]

theorem dg_unit (x : GL (Fin a) R) (y : GL (Fin b) R) : IsUnit (dg x.val y.val) := by
  rw [Matrix.isUnit_iff_isUnit_det, dg_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)

end Blocks

variable {g : ℕ} [Fact g.Prime] {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem inc_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (inc g n k).val = k.val.map (algebraMap ℤ_[g] ℚ_[g]) := rfl

theorem red_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (red g n k).val = k.val.map (PadicInt.toZMod (p := g)) := rfl

theorem det_inc (n : ℕ) (k : GL (Fin n) ℤ_[g]) : Matrix.GeneralLinearGroup.det (inc g n k) =
    Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, inc_val, Units.coe_map]
  exact ((algebraMap ℤ_[g] ℚ_[g]).map_det k.val).symm

variable {π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
  {ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ} {Λ : V →ₗ[ℂ] W} {χ : (ZMod g)ˣ →* ℂˣ}

theorem blk_val (x : Gn g a) (y : Gn g b) : (blk a b (a + b) x y).val = dg x.val y.val := by
  have hu := dg_unit x y
  change (toG (dg x.val y.val)).val = _
  rw [toG, dif_pos hu, IsUnit.unit_spec]

end GlobalTheory.GLp.ParInd
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

theorem eigSum_good_sup_compl_eq_top : ∀ (D : D7) (i : D.nd.Loc), ZRat D (D.nd.mu i) (D.nd.j i) → SpecPr D i →
    D.nd.eigSum i ↑(D.nd.Zgood i) ⊔ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ = ⊤ := by
  intro D i hZ hS
  rw [eq_top_iff, ← D.nd.prMt_span i, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i)) ⊔
      ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ := by
    unfold ZRat at hZ
    rw [hZ]; exact Submodule.mem_top
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hS.1 u hu) (hS.2 u' hu')

end GlobalTheory.EtaJoin
end
