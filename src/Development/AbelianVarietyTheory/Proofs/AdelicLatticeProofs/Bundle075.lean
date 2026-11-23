module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem tNorm_baseChange_of_ringHom (F F' E E' K K' : Type) [Field F] [Field F'] [Field E]
    [Field E'] [Algebra F F'] [Algebra F E] [Algebra F' E'] [Algebra E E'] [Algebra F E']
    [IsScalarTower F F' E'] [IsScalarTower F E E'] [Algebra.IsPushout F F' E E']
    [FiniteDimensional F E] [Field K] [Algebra F K] [Field K'] [Algebra F' K'] (φ : K →+* K')
    (hφ : ∀ x : F, φ (algebraMap F K x) = algebraMap F' K' (algebraMap F F' x)) (x : F)
    (h : TNorm F E K x) : TNorm F' E' K' (algebraMap F F' x) := by
  letI : Algebra F K' := ((algebraMap F' K').comp (algebraMap F F')).toAlgebra
  haveI : IsScalarTower F F' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨y₀, hy₀⟩ := h
  let ψ : K →ₐ[F] K' := { φ with commutes' := hφ }
  let y : K' ⊗[F] E := Algebra.TensorProduct.map ψ (AlgHom.id F E) y₀
  have hy : Algebra.norm K' y = algebraMap F K' x := by
    rw [tensor_norm_map ψ y₀, hy₀, AlgHom.commutes]
  let e₁ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F] E :=
    Algebra.TensorProduct.cancelBaseChange F F' K' K' E
  let e₂ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F'] E' :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.IsPushout.equiv F F' E E')
  refine ⟨(e₁.symm.trans e₂) y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv, hy, ← IsScalarTower.algebraMap_apply]

theorem exists_norm_eq_of_coprime_pow {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {m n : ℕ} (hc : Nat.Coprime m n) {x : F} (hx : x ≠ 0) {a b : E}
    (ha : Algebra.norm F a = x ^ m) (hb : Algebra.norm F b = x ^ n) :
    ∃ y : E, Algebra.norm F y = x := by
  refine ⟨a ^ (Nat.gcdA m n) * b ^ (Nat.gcdB m n), ?_⟩
  rw [map_mul, Algebra.norm_zpow, Algebra.norm_zpow, ha, hb, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ hx, ← Nat.gcd_eq_gcd_ab, hc]
  simp

theorem np_of_odd_prime_degree : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E],
    p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ hp h2 hd x hx hl
  obtain ⟨F', E', _, _, _, _, _, _, _, _, _, _, ζ, hpo, htc, hg, hζ, hd', hc⟩ :=
    exists_pushout_primitiveRoot p F E hp h2 hd
  have hl' : LocNorm F' E' (algebraMap F F' x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F F' w
      exact tNorm_baseChange_of_ringHom F F' E E' _ _ φ hφ x (hl.1 _)
    · exfalso
      let ψ : F' →+* ℂ := Complex.ofRealHom.comp (algebraMap F' ℝ)
      apply IsTotallyComplex.complexEmbedding_not_isReal ψ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      simp [ψ]
  obtain ⟨b, hb⟩ :=
    np_of_finrank_prime_of_isPrimitiveRoot p F' E' ζ hp hζ hd' _ (by simpa using hx) hl'
  have h1 : Algebra.norm F (Algebra.norm E b) = x ^ Module.finrank F F' := by
    rw [Algebra.norm_norm, ← Algebra.norm_norm (S := F'), hb, Algebra.norm_algebraMap]
  have h3 : Algebra.norm F (algebraMap F E x) = x ^ p := by
    rw [Algebra.norm_algebraMap, hd]
  exact exists_norm_eq_of_coprime_pow hc hx h1 h3

end GlobalTheory.CNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.VacUnique.Ann

theorem deriv_twisted_line {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] (F : R → ℂ) (hF : Differentiable ℝ F)
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (w u : R) :
    deriv (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om w (t • u) : ℂ)) * F (w + t • u)) 0 =
      fderiv ℝ F w u - Real.pi * Complex.I * (om w u : ℂ) * F w := by
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 : HasDerivAt (fun t : ℝ => F (w + t • u)) (fderiv ℝ F w u) 0 := by
    have h := (hF (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * (om w (t • u) : ℂ))
      (-(Real.pi * Complex.I) * (om w u : ℂ)) 0 := by
    have e : (fun t : ℝ => -(Real.pi * Complex.I) * (om w (t • u) : ℂ)) =
        fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * (om w u : ℂ)) := by
      funext t
      rw [LinearMap.map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (-(Real.pi * Complex.I) * (om w u : ℂ))
  have h4 := (h3.cexp.mul h2).deriv
  refine Eq.trans h4 ?_
  simp only [zero_smul, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul]
  ring

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

open Classical in
theorem lineAt_eq (h : Chart θ σ) (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ z t = iotaW σ T S (t • (Pi.single τ z : RW T S)) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ h.inf T.rank S.rank τ z)
  refine h.real_ext (V := T) (W := S) (hL.2.1 t) (h.real_iota T S _) ?_
  rw [h.pi_iota]
  funext τ'
  refine (hL.2.2 t τ').trans ?_
  by_cases e : τ' = τ
  · subst e
    have e1 : (Pi.single τ' z : RW T S) τ' = z := Pi.single_eq_same _ _
    rw [if_pos rfl, Pi.smul_apply, e1]
    funext i j
    show (t : ℂ) * z i j = t • z i j
    exact (Complex.real_smul).symm
  · have e1 : (Pi.single τ z : RW T S) τ' = 0 := Pi.single_eq_of_ne e _
    rw [if_neg e, Pi.smul_apply, e1, smul_zero]
    rfl

open Classical in
theorem dRho_eq (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (hF : Differentiable ℝ fun z : RW T S => f (iotaW σ T S z)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : RW T S) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f (iotaW σ T S w) =
      fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (Pi.single τ z) -
        Real.pi * Complex.I * (omO S T w (Pi.single τ z) : ℂ) * f (iotaW σ T S w) := by
  refine Eq.trans ?_ (deriv_twisted_line _ hF (omO S T) w (Pi.single τ z))
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [lineAt_eq h S T τ z t]
  unfold heisO
  rw [GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inl (h.real_iota T S w)), h.pi_iota, h.pi_iota,
    (iotaW σ T S).map_add]

open Classical in
theorem jO_single (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    jO S T sS sT (Pi.single τ z) = Pi.single τ (cplxO (sS τ) (sT τ) z) := by
  funext τ'
  rw [jO_apply]
  by_cases e : τ' = τ
  · subst e
    have e1 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ, (Pi.single τ' y : RW T S) τ' = y :=
      fun _ => Pi.single_eq_same _ _
    rw [e1, e1]
  · have e1 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ, (Pi.single τ y : RW T S) τ' = 0 :=
      fun _ => Pi.single_eq_of_ne e _
    rw [e1, e1]
    show Complex.I • (sT τ' * (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) * sS τ') = (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    rw [Matrix.mul_zero, Matrix.zero_mul, smul_zero]

theorem vacuum_annihilation : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) ∧ ∀ w z : RW T S, (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z - Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)) + Complex.I * (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (jO S T sS sT z) - Real.pi * Complex.I * (omO S T w (jO S T sS sT z) : ℂ) * f (iotaW σ T S w)) = 0 := by
  classical
  intro D θ σ h ψ hψ S T sS sT f hf hv
  have hF : Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) := by
    have h1 := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth 0
    simp only [zero_add] at h1
    exact h1.differentiable (by simp)
  refine ⟨hF, fun w z => ?_⟩
  let A : RW T S →+ ℂ :=
    { toFun := fun z => fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z -
        Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)
      map_zero' := by simp
      map_add' := fun x y => by
        rw [ContinuousLinearMap.map_add (f := _), LinearMap.map_add (f := _), Complex.ofReal_add]
        ring }
  show A z + Complex.I * A (jO S T sS sT z) = 0

  rw [← Finset.univ_sum_single z, map_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun τ _ => ?_
  have h1 := congrFun (hv τ (z τ)) (iotaW σ T S w)
  have h2 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z τ) f (iotaW σ T S w) +
      Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) (z τ)) f (iotaW σ T S w) = 0 := h1
  have h3 := dRho_eq h hψ S T f hF τ (z τ) w
  have h4 := dRho_eq h hψ S T f hF τ (cplxO (sS τ) (sT τ) (z τ)) w
  have h5 := jO_single S T sS sT τ (z τ)
  have h6 : A (Pi.single τ (z τ)) + Complex.I * A (Pi.single τ (cplxO (sS τ) (sT τ) (z τ))) = 0 :=
    (congrArg₂ (fun a b : ℂ => a + Complex.I * b) h3 h4).symm.trans h2
  exact (congrArg (fun b => A (Pi.single τ (z τ)) + Complex.I * A b) h5).trans h6

end GlobalTheory.VacUnique.Ann
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorL_intertwine {ι X : Type} (p : (X → ℂ) → Prop) (p0 : p 0) (padd : ∀ a b, p a → p b → p (a + b))
    (psmul : ∀ (c : ℂ) a, p a → p (c • a)) (A A' : ι → (X → ℂ) → (X → ℂ)) (Φ : Module.End ℂ (X → ℂ))
    (hA : ∀ i f, p f → p (A i f) ∧ Φ (A i f) = A' i (Φ f)) (f : X → ℂ) (hf : p f) (P : MvPolynomial ι ℂ) :
    p (pureTensorL A f P) ∧ Φ (pureTensorL A f P) = pureTensorL A' (Φ f) P := by
  have hl : ∀ l : List ι, p (l.foldr (fun i g => A i g) f) ∧
      Φ (l.foldr (fun i g => A i g) f) = l.foldr (fun i g => A' i g) (Φ f) := by
    intro l
    induction l with
    | nil => exact ⟨hf, rfl⟩
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih.2]
      exact hA i _ ih.1
  have hm : ∀ (B : ι → (X → ℂ) → (X → ℂ)) (g : X → ℂ) (k : ι →₀ ℕ) (c : ℂ),
      pureTensorL B g (MvPolynomial.monomial k c) = c • opPow B k g := by
    intro B g k c
    have e : MvPolynomial.monomial k c = c • MvPolynomial.basisMonomials ι ℂ k := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
  induction P using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [hm, hm, map_smul]
    exact ⟨psmul c _ (hl _).1, congrArg (c • ·) (hl _).2⟩
  | add P Q hP hQ =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hP.2, hQ.2]
    exact ⟨padd _ _ hP.1 hQ.1, rfl⟩

theorem cplxO_move {m n : ℕ} {sS sS' G G' : Matrix (Fin n) (Fin n) ℂ} {sT sT' H : Matrix (Fin m) (Fin m) ℂ}
    (hG : G * G' = 1) (hS : sS' * G = G * sS) (hT : sT' * H = H * sT) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO sS' sT' (H * z * G') = H * cplxO sS sT z * G' := by
  have hG' : G' * G = 1 := mul_eq_one_comm.1 hG
  have e : G' * sS' = sS * G' := by
    calc G' * sS' = G' * (sS' * G) * G' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.mul_one]
      _ = sS * G' := by rw [hS, ← Matrix.mul_assoc, hG', Matrix.one_mul]
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc sT' * (H * z * G') * sS' = (sT' * H) * z * (G' * sS') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, e]; simp only [Matrix.mul_assoc]

theorem unitMap_move {m n : ℕ} {B G G' : Matrix (Fin n) (Fin n) ℂ} {B' H : Matrix (Fin m) (Fin m) ℂ}
    (hG : G * G' = 1) (i : Fin m) (j : Fin n) : unitMap (G * B) (H * B') i j = H * unitMap B B' i j * G' := by
  unfold unitMap
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hG]
  simp only [Matrix.mul_assoc]

theorem om_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS sS' BS BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT sT' BT BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (g : GA D S) (h : GA D T), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → (∀ τ, BS' τ = compAt θ τ (mt S g) * BS τ) → (∀ τ, BT' τ = compAt θ τ (mt T h) * BT τ) → ∀ f, IsThetaFunO ψ S T f → ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) ∧ om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS' sT' BS' BT' (om (g, h) f) P := by
  intro D ψ θ S T χS χT om hom hθ sS sS' BS BS' sT sT' BT BT' g h h1 h2 h3 h4 f hf P
  refine pureTensorL_intertwine (IsThetaFunO ψ S T) theta_zero (fun _ _ => theta_add) (fun c _ => theta_smul c) _ _
    (om (g, h)) (fun k f hf => ?_) f hf P
  obtain ⟨τ, i, j⟩ := k
  have hG := compAt_mt_mul_inv (θ := θ) τ g
  refine ⟨theta_smul _ (theta_sub (theta_dRho hθ hom.std τ _ hf) (theta_smul _ (theta_dRho hθ hom.std τ _ hf))), ?_⟩
  simp only [aPlusAll, aPlus, crea]
  rw [map_smul, map_sub, map_smul, om_dRho hom hθ g h τ _ hf, om_dRho hom hθ g h τ _ hf, h3, h4, unitMap_move hG,
    cplxO_move hG (h1 τ) (h2 τ)]

end GlobalTheory.OrientedHeis

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous : ∀ (D : D7) (S T : HSp D), (∀ x y z : WO S T, symplOH S T (x + y) z = symplOH S T x z + symplOH S T y z) ∧ (∀ x y z : WO S T, symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z) ∧ (∀ x : WO S T, symplOH S T x x = 0) ∧ (∀ x y : WO S T, symplOH S T x y + symplOH S T x y = symplO S T x y) ∧ Continuous (fun q : WO S T × WO S T => symplOH S T q.1 q.2) ∧ (∀ g ∈ ratL T S, ∀ g' ∈ ratL T S, ∃ a : D.host.F, symplOH S T g g' = algebraMap D.host.F (AF D.host.F) a) ∧ (∀ (a : AE D) (x y : WO S T), symplOH S T (x.map fun z => a * z) y = symplOH S T x (y.map fun z => cA D a * z)) ∧ (∀ (e a : AE D) (u : WO S T), e * cA D e = 0 → IsHalf e u → symplOH S T (u.map fun z => a * z) u = 0) ∧ ∀ x y : WO S T, x.map (finPart D) = 0 → y.map (infPart D) = 0 → symplOH S T x y = 0 := by
  first | exact @GlobalTheory.OrientedFormLaws.symplOH_laws | exact GlobalTheory.OrientedFormLaws.symplOH_laws | (intros; apply GlobalTheory.OrientedFormLaws.symplOH_laws <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem actO_two_nsmul (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (2 • x) = 2 • actO S T g h x := by
  rw [two_nsmul, two_nsmul, actO_add]

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem isHalf_actO (e : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have e1 : e • x = x := Matrix.ext hx
  have e2 : e • actO S T g h x = actO S T g h x := by
    unfold actO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, e1]
  exact fun i j => congrFun (congrFun e2 i) j

theorem sqNormIntegralFundamentalDomain_eq_l2Norm_sq (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {f : WO S T → ℂ} (hf : Continuous f) :
    nrm2 μ 𝓕 f = (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ).toReal := by
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  unfold nrm2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => sq_nonneg _)
    (hf.norm.pow 2).measurable.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem isVacO_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS sS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT sT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS LS' : Set (Fin S.rank → D.host.E)) (LT LT' : Set (Fin T.rank → D.host.E)) (g : GA D S) (h : GA D T), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → (∀ u : WO S T, u ∈ (latO S T LS' LT' fun _ => True) ↔ ∃ u₀ ∈ (latO S T LS LT fun _ => True), u = actO S T g h u₀) → ∀ f, IsVacO ψ θ S T sS sT LS LT f → IsVacO ψ θ S T sS' sT' LS' LT' (om (g, h) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sS' sT sT' LS LS' LT LT' g h hS hT hΛ f hf
  obtain ⟨hψ, -, hth, hlat, hfock, hnorm⟩ := hf
  refine ⟨hψ, hθ, hW.om_pres _ _ hth, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, hnorm.1, fun p hp => ?_⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← actO_two_nsmul, ← hW.om_heis g h _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := isHalf_actO e g⁻¹ h⁻¹ hh
      rwa [actO_inv_actO] at this
    rw [← hW.om_heis g h _ f hth, hlat.2 e he u₀ hu₀ h0]
  · obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin T.rank) (Fin S.rank) ℂ, z = compAt θ τ (mt T h) * z₀ * compAt θ τ (mt S g⁻¹) := by
      refine ⟨compAt θ τ (mt T h⁻¹) * z * compAt θ τ (mt S g), ?_⟩
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        compAt_mt_mul_inv, Matrix.mul_one]
    have h0 := congrArg (om (g, h)) (hfock τ z₀)
    unfold annih at h0 ⊢
    rw [map_add (f := _), map_smul, map_zero, om_dRho hW hθ g h τ _ hth, om_dRho hW hθ g h τ _ hth] at h0
    rw [cplxO_move θ τ g h (hS τ) (hT τ)]
    exact h0
  · show nrm2 p.1 p.2 (om (g, h) f) = 1
    rw [sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ (hW.om_pres _ _ hth).cont, hW.om_unit p.1 p.2 hp.1 hp.2.1 _ f hth, ← sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hth.cont]
    exact hnorm.2 p hp

end GlobalTheory.WeilVacMove

end
end

section

open HeckeCharacterZeroLocus.ThmBIn NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeInhabitant

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_fin : ∃ Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E, Continuous Φ ∧
    (∀ x, Φ (incA F E x) = algebraMap E _ x) ∧
    ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1 := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine ⟨ι.toRingHom.comp (finPart F E), ?_, fun x => h1 x, fun y => h2 _⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have := GlobalTheory.HeckeTensorRead.continuous_of_map_integral
    (ι.toRingHom.comp (algebraMap (Af F) (Af F ⊗[F] E))) (fun a ha P =>
      (h2 (a ⊗ₜ[F] (1 : E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P)
  exact this.comp continuous_snd

theorem cA_inc (σ : E →ₐ[F] E) (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) x P) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

end General

end GlobalTheory.HeckeInhabitant
end
