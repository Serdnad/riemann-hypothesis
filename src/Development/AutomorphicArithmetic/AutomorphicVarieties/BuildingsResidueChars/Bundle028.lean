module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEigenvectorOfRoot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle023
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsBdd
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle020
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing
public import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
public import GroundTheory.AutomorphicForms.GKModules.Garding

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

private theorem map_pow_of_commuting {R S M N : Type} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] (f : M → N) (a : Module.End R M) (b : Module.End S N)
    (hf : ∀ x, f (a x) = b (f x)) (n : ℕ) (x : M) : f ((a ^ n) x) = (b ^ n) (f x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hf]

private theorem aeval_restriction_commute {F L M : Type} [Field F] [Field L] [Algebra F L] [AddCommGroup M] [Module L M]
    [Module F M] [IsScalarTower F L M] (D : Submodule L M) (S : Module.End L D) (T : Module.End F M)
    (hf : ∀ x : D, ((S x : D) : M) = T x) (q : F[X]) (x : D) :
    ((aeval S (q.map (algebraMap F L)) x : D) : M) = aeval T q (x : M) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, Submodule.coe_add, hp, hr]
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
      algebraMap_smul, map_pow_of_commuting (fun x : D => (x : M)) S T hf]

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

private theorem mem_aux {x : V ⊗[ℚ_[l]] P.R.B} : x ∈ Dcris (P.PD K) ρ ↔ ∀ g, actVB (P.PD K) ρ g x = x := by
  simp [Dcris, sub_eq_zero]

private theorem pullback_fin_relation [FiniteDimensional ↥LL.1 V] (hC : IsCrys (P.PD K) ρ) :
    FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) := by
  rcases subsingleton_or_nontrivial V with hs | hn
  · haveI : Subsingleton (V ⊗[ℚ_[l]] P.R.B) := inferInstance
    infer_instance
  · haveI := (P.PD K).finK₀
    apply Module.finite_of_finrank_pos
    rw [hC]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

private theorem frobenius_preserves_crystalline : ∀ x ∈ Dcris (P.PD K) ρ,
    φVB (P.PD K) (LL := ↥LL.1) (V := V) x ∈ Dcris (P.PD K) ρ := by
  intro x hx
  rw [mem_aux] at hx ⊢
  intro g
  have : ∀ y, actVB (P.PD K) ρ g (φVB (P.PD K) (LL := ↥LL.1) (V := V) y) =
      φVB (P.PD K) (LL := ↥LL.1) (V := V) (actVB (P.PD K) ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [actVB, φVB, (P.PD K).φ_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [this, hx]

private theorem crystalline_mem_potentially_semistable : ∀ x ∈ Dcris (P.PD K) ρ, crisIncl P ↥LL.1 V x ∈ Dpst P ρ := by
  intro x hx
  exact (mem_Dpst P ρ).mpr ⟨K, fun g _ => by rw [stRep_crisIncl, (mem_aux P ρ).mp hx g]⟩

private noncomputable def crystallineInclusion : ↥(Dcris (P.PD K) ρ) →ₗ[↥LL.1] ↥(Dpst P ρ) :=
  (crisIncl P ↥LL.1 V).restrict (crystalline_mem_potentially_semistable P ρ)

private theorem coe_crystalline_inclusion (x : ↥(Dcris (P.PD K) ρ)) :
    ((crystallineInclusion P ρ x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x := rfl

private noncomputable def frobeniusRestriction : Module.End ↥LL.1 ↥(Dcris (P.PD K) ρ) :=
  (φVB (P.PD K) (LL := ↥LL.1) (V := V)).restrict (frobenius_preserves_crystalline P ρ)

private theorem coe_frobenius_restriction_pow (n : ℕ) (x : ↥(Dcris (P.PD K) ρ)) :
    (((frobeniusRestriction P ρ ^ n) x : ↥(Dcris (P.PD K) ρ)) : V ⊗[ℚ_[l]] P.R.B) =
      ((φVB (P.PD K) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ n) x :=
  map_pow_of_commuting (fun x : ↥(Dcris (P.PD K) ρ) => x.1) (frobeniusRestriction P ρ)
    (φVB (P.PD K) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) (fun _ => rfl) n x

private theorem coe_frobenius_restriction_pow_base (n : ℕ) (x : ↥(Dcris (P.PD K) ρ)) :
    (((frobeniusRestriction P ρ ^ n) x : ↥(Dcris (P.PD K) ρ)) : V ⊗[ℚ_[l]] P.R.B) =
      ((φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ n) x :=
  map_pow_of_commuting (fun x : ↥(Dcris (P.PD K) ρ) => x.1) (frobeniusRestriction P ρ)
    (φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) (fun _ => rfl) n x

private noncomputable def crystallineToWeilDeligne (ι : Om l ≃+* ℂ) : ↥(Dcris (P.PD K) ρ) →+ WDSpace P ι ρ :=
  AddMonoidHom.mk' (fun x => wdMk P ι ρ (crystallineInclusion P ρ x)) fun x y => by rw [map_add (f := _), wdMk_add]

private theorem span_crystalline_weil_deligne_top [FiniteDimensional ↥LL.1 V] (ι : Om l ≃+* ℂ) (hV : IsPst P ρ) (hC : IsCrys (P.PD K) ρ) :
    Submodule.span ℂ (Set.range (crystallineToWeilDeligne P ρ ι)) = ⊤ := by
  rw [eq_top_iff, ← UpperTheory.weil_deligne_span_crystalline P ι ρ hV hC]
  refine Submodule.span_mono ?_
  rintro z ⟨x, y, hx, hy, rfl⟩
  exact ⟨⟨x, hx⟩, congrArg (wdMk P ι ρ) (Subtype.ext hy.symm)⟩

private theorem eval_root_transport (ι : Om l ≃+* ℂ) (b : ℂ) (q : ℚ_[l][X]) (hq : aeval (ι.symm b) q = 0) :
    (q.map (algebraMap ℚ_[l] ↥LL.1)).eval₂ (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) b = 0 := by
  rw [eval₂_map]
  have h1 := congrArg ι.toRingHom hq
  rw [map_zero, aeval_def, hom_eval₂] at h1
  have e1 : (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))).comp (algebraMap ℚ_[l] ↥LL.1) =
      ι.toRingHom.comp (algebraMap ℚ_[l] (Om l)) := by
    rw [IsScalarTower.algebraMap_eq ℚ_[l] ↥LL.1 (Om l)]; rfl
  rw [e1]
  simpa using h1

set_option synthInstance.maxHeartbeats 100000 in
private theorem crystalline_to_weil_deligne_smul (ι : Om l ≃+* ℂ) (a : ↥LL.1) (x : ↥(Dcris (P.PD K) ρ)) :
    crystallineToWeilDeligne P ρ ι (a • x) = (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) a • crystallineToWeilDeligne P ρ ι x :=
  (congrArg (wdMk P ι ρ) ((crystallineInclusion P ρ).map_smul a x)).trans (wdMk_smul P ι ρ a _)

set_option synthInstance.maxHeartbeats 100000 in
private theorem fin_step (n : ℕ) (q : ℚ_[l][X])
    (H : ∃ x : ↥(Dcris (P.PD K) ρ), x ≠ 0 ∧ aeval (frobeniusRestriction P ρ ^ n) (q.map (algebraMap ℚ_[l] ↥LL.1)) x = 0) :
    ∃ x ∈ Dcris (P.PD K) ρ, x ≠ 0 ∧
      aeval ((φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ n) q x = 0 := by
  obtain ⟨x, hx0, hx⟩ := H
  refine ⟨x.1, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  exact (aeval_restriction_commute (Dcris (P.PD K) ρ) (frobeniusRestriction P ρ ^ n) _ (coe_frobenius_restriction_pow_base P ρ n) q x).symm.trans
    (congrArg Subtype.val hx)

end SlopeTestRemainingChoices

theorem UpperTheory.crystalline_of_place_over :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V), IsPst P ρ → IsCrys (P.PD Bw.Kw) ρ → ∀ σ : ↥(Weil h), deg σ = -1 → ∀ b ∈ (wdPst P ι Bw h hj ρ).eig σ, ∀ q : ℚ_[l][X], aeval (ι.symm b) q = 0 → ∃ x ∈ Dcris (P.PD Bw.Kw) ρ, x ≠ 0 ∧ aeval ((φVB (P.PD Bw.Kw) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ resDeg l w) q x = 0 := by
  intro l _ P ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj LL V _ _ _ _ _ ρ hV hC σ hσ b hb q hq
  haveI := hV.finite
  haveI := pullback_fin_relation P ρ hC
  have hb' : b ∈ (wdRho P ι Bw h hj ρ σ).charpoly.roots := by
    rw [← GlobalTheory.Pst.DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ]
    exact hb
  have hT : ∀ x, wdRho P ι Bw h hj ρ σ (crystallineToWeilDeligne P ρ ι x) = crystallineToWeilDeligne P ρ ι ((frobeniusRestriction P ρ ^ resDeg l w) x) := fun x =>
    (wdRho_mk P ι Bw h hj ρ σ (crystallineInclusion P ρ x)).trans (congrArg (wdMk P ι ρ) (Subtype.ext
      ((UpperTheory.local_crystalline_of_induced P Bw h hj ρ σ hσ x.1 (crystallineInclusion P ρ x) x.2 (coe_crystalline_inclusion P ρ x)).trans
        ((coe_crystalline_inclusion P ρ _).trans (congrArg (crisIncl P ↥LL.1 V) (coe_frobenius_restriction_pow P ρ _ x))).symm)))
  exact fin_step P ρ _ q (UpperTheory.exists_eigenvector_of_root (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (crystallineToWeilDeligne P ρ ι)
    (frobeniusRestriction P ρ ^ resDeg l w) (wdRho P ι Bw h hj ρ σ) (crystalline_to_weil_deligne_smul P ρ ι)
    (span_crystalline_weil_deligne_top P ρ ι hV hC) hT (q.map (algebraMap ℚ_[l] ↥LL.1)) b hb' (eval_root_transport ι b q hq))
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def extL (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) :
    archLie K a →ₗ[ℝ] archLie K n where
  toFun Y := (isExpLieAlgebra K n).ofLie (toLie K n (ext0 e (mat Y.1)))
  map_add' X Y := Subtype.ext (matrixExtendByZero_add e (mat X.1) (mat Y.1))
  map_smul' c X := Subtype.ext (by
    change ext0 e (c • mat X.1) = c • ext0 e (mat X.1)
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul])

private theorem key (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K n) (ψ : AdelicGLn.AdelicGL K n → ℂ) (m : AdelicGLn.AdelicGL K a) (x : archGroup K a)
    (Y : archLie K a) :
    archSlice (fun m => ψ (g * emb e m)) m (x * (isExpLieAlgebra K a).expG Y) =
      archSlice ψ (g * emb e m) (embArch e x * (isExpLieAlgebra K n).expG (extL K e Y)) := by
  obtain ⟨h1, h2⟩ := UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e
  have h3 : embArch e ((isExpLieAlgebra K a).expG Y) = (isExpLieAlgebra K n).expG (extL K e Y) := h2 (mat Y.1)
  rw [← h3, ← map_mul, archSlice_apply, archSlice_apply, ← h1, map_mul (emb e) m, mul_assoc]

theorem UpperTheory.exists_restriction_blockEmbedding_intertwines_lie :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K n), ∃ f : archSmooth K n →ₗ[ℂ] archSmooth K a, (∀ ψ m, (f ψ).1 m = ψ.1 (g * emb e m)) ∧ ∀ X ψ, f (lam K n (ext0 e X) ψ) = lam K a X (f ψ) := by
  intro K _ _ a n e g
  have hs : ∀ ψ : archSmooth K n, (fun m => ψ.1 (g * emb e m)) ∈ archSmooth K a := fun ψ m => by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro x
    simp only [key]
    exact (((isExpLieAlgebra K n).isSmoothFun_iff).1 (ψ.2 (g * emb e m)) (embArch e x)).comp
      (LinearMap.toContinuousLinearMap (extL K e)).contDiff
  refine ⟨{ toFun := fun ψ => ⟨_, hs ψ⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun _ _ => rfl, fun X ψ => Subtype.ext (funext fun m => ?_)⟩
  have h1 := (isExpLieAlgebra K a).hasDerivAt_rightDeriv (hs ψ m) ((isExpLieAlgebra K a).ofLie (toLie K a X)) 1
  have h2 := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (ψ.2 (g * emb e m))
    (extL K e ((isExpLieAlgebra K a).ofLie (toLie K a X))) 1
  simp only [key, map_one, map_smul] at h1
  exact (uAction_ι_apply (toLie K n (ext0 e X)) ψ (g * emb e m)).trans
    ((h2.unique h1).trans (uAction_ι_apply (toLie K a X) ⟨_, hs ψ⟩ m).symm)
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem blk_mul_blk_inv {r s : ℕ} {R : Type} [CommRing R] (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R) :
    blk m₁ m₂ * blk m₁⁻¹ m₂⁻¹ = 1 := by
  simp only [blk]
  rw [emb_comm m₁⁻¹ m₂⁻¹, map_inv, map_inv]
  group

theorem UpperTheory.constantTerm_levi_rational_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (φ : AdelicGLn.AdelicGL K (r + s) → ℂ),
      IsLeftInvariant φ → ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g,
        constantTerm (r := r) φ (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) =
          constantTerm (r := r) φ g := by
  intro K _ _ r s φ hφ γ₁ γ₂ g
  have hdiag : ∀ γ : GL (Fin (r + s)) K, AdelicGLn.diagonal K (r + s) γ =
      GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) γ := fun _ => rfl
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁ γ₂
  obtain ⟨c', hc'⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁⁻¹ γ₂⁻¹
  have hDD : AdelicGLn.diagonal K (r + s) (blk γ₁⁻¹ γ₂⁻¹) = (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    rw [← map_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_right (blk_mul_blk_inv γ₁ γ₂)
  have hu : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * Y q) =
        (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ * unipGL Y * AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) := by
    intro Y
    have h := hc' (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag, hDD] at h
    rw [h]
    group
  have hv : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * Y q) =
        AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * unipGL Y * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    intro Y
    have h := hc (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag] at h
    rw [h]
    group
  have hmem : ∀ (d : UPos (r + s) r → UPos (r + s) r → K) (X : UPos (r + s) r → AdeleRing (𝓞 K) K),
      X ∈ unipLattice K (r + s) r →
        (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) ∈ unipLattice K (r + s) r := by
    intro d X hX
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hX
    refine AddMonoidHom.mem_range.mpr ⟨fun p => ∑ q, d p q * y q, ?_⟩
    funext p

    simp [AddMonoidHom.compLeft_apply, map_sum, map_mul]
  have hcont : ∀ d : UPos (r + s) r → UPos (r + s) r → K,
      Continuous (fun (X : UPos (r + s) r → AdeleRing (𝓞 K) K) p =>
        ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) := by
    intro d
    refine continuous_pi fun p => ?_
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_apply q)
  have hinv1 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c' q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hv, hu]
    group
  have hinv2 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hu, hv]
    group
  let α : (UPos (r + s) r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos (r + s) r → AdeleRing (𝓞 K) K) :=
    { toFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q
      invFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * X q
      left_inv := fun X => hinv1 X
      right_inv := fun X => hinv2 X
      map_add' := by
        intro X Y
        funext p
        simp [mul_add, Finset.sum_add_distrib]
      continuous_toFun := hcont c'
      continuous_invFun := hcont c }
  have hα : ∀ X, α X ∈ unipLattice K (r + s) r ↔ X ∈ unipLattice K (r + s) r := by
    intro X
    constructor
    · intro h
      have h2 := hmem c (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) h
      rwa [hinv1] at h2
    · exact hmem c' X
  have hper : ∀ ξ ∈ unipLattice K (r + s) r, ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL (ξ + X) * g) = φ (unipGL X * g) :=
    fun ξ hξ X => hφ.unipGL_vadd g ⟨ξ, hξ⟩ X
  have hstep : ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL X * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g)) = φ (unipGL (α X) * g) := by
    intro X
    rw [← hφ (blk γ₁⁻¹ γ₂⁻¹), hDD]
    change _ = φ (unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) * g)
    rw [hu]
    group
  unfold constantTerm
  simp_rw [hstep]
  exact UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving K (r + s) r α hα (fun X => φ (unipGL X * g)) hper
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

private theorem step_of_mult [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (c : ℤ)
    (h : ∀ τ : K →ₐ[Qp] LL, multV PD ρ τ c = 0) :
    DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (c + 1) = DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) c := by
  rw [JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ (c + 1), JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ c]
  refine iSup_congr fun τ => ?_
  have hle : FildR PD ρ τ c ≤ DdR PD ρ := fun x hx => hx.1.1
  have : FiniteDimensional LL ↥(FildR PD ρ τ c) := Submodule.finiteDimensional_of_le hle
  have h0 := h τ
  unfold multV at h0
  refine Submodule.eq_of_le_of_finrank_eq (Ln03.Pf.jb_FildR_anti PD ρ τ (by omega)) ?_
  omega

private theorem gen_fil [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) :
    (∀ a : ℤ, (∀ (τ : K →ₐ[Qp] LL) (c : ℤ), c < a → multV PD ρ τ c = 0) →
      DdR PD ρ ≤ FilV PD (LL := LL) (V := V) a) ∧
    ∀ b : ℤ, (∀ (τ : K →ₐ[Qp] LL) (c : ℤ), b < c → multV PD ρ τ c = 0) →
      DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (b + 1) = ⊥ := by
  refine ⟨fun a ha x hx => ?_, fun b hb => ?_⟩
  · obtain ⟨c, hc⟩ := Ln03.Pf.jb_FilV_exh PD (LL := LL) (V := V) x
    rcases le_total a c with h | h
    · exact Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hc
    · have key : ∀ d, c ≤ d → d ≤ a → x ∈ FilV PD (LL := LL) (V := V) d := by
        intro d hd
        induction d, hd using Int.leInduction with
        | base => exact fun _ => hc
        | succ d hd ih =>
          intro hda
          have hm : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) d := ⟨hx, ih (by omega)⟩
          rw [← step_of_mult PD hcard ρ hfin d fun τ => ha τ d (by omega)] at hm
          exact hm.2
      exact key a h le_rfl
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine Ln03.Pf.jb_FilV_sep PD (LL := LL) (V := V) x fun d => ?_
    rcases le_total d (b + 1) with h | h
    · exact Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hx.2
    · induction d, h using Int.leInduction with
      | base => exact hx.2
      | succ d hd ih =>
        have hm : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) d := ⟨hx.1, ih⟩
        rw [← step_of_mult PD hcard ρ hfin d fun τ => hb τ d (by omega)] at hm
        exact hm.2

end Gen

theorem UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1) → ∀ {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) → (∀ a : ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ), c < a → multV (P.PD K) ρ τ c = 0) → DdR (P.PD K) ρ ≤ FilV (P.PD K) (LL := ↥LL.1) (V := V) a) ∧ ∀ b : ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ), b < c → multV (P.PD K) ρ τ c = 0) → DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) (b + 1) = ⊥ := by
  intro l _ P K LL key V _ _ _ _ _ ρ hfin
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
    let e : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≃ (↥K.1 →ₐ[ℚ_[l]] Om l) :=
      { toFun := fun f => LL.1.val.comp f
        invFun := fun g => g.codRestrict LL.1.toSubalgebra (key g)
        left_inv := fun f => by ext; rfl
        right_inv := fun g => by ext; rfl }
    rw [Nat.card_congr e]
    exact AlgHom.natCard_of_splits _ _ _ (fun _ => IsAlgClosed.splits _)
  have : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  exact gen_fil (P.PD K) (by rw [Fintype.card_eq_nat_card, hc]) ρ hfin
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_archSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : archSmooth K n), IsAutomorphicForm φ.1 → ∃ hs : IsArchSmooth (constantTerm r φ.1), ∀ X : (isExpLieAlgebra K n).lieSubalgebra, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) ⟨constantTerm r φ.1, hs⟩).1 = constantTerm r (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 := by
  intro K _ _ n r φ hφ
  let μ : Measure (archGroup K n) := Measure.haar
  obtain ⟨d, b, ε, B, h1, h2, h3, h4, h5⟩ := exists_archCartanData K n
  obtain ⟨P, hPm, hPd, hP⟩ :=
    hφ.isSmoothKZ.exists_aeval_laplacian_sliceL_eq_zero b ε B h1 h2 h3 h4 h5
  obtain ⟨κ, hκs, hκc, -, hκ⟩ :=
    (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd
      (U := Set.univ) Filter.univ_mem
  have hκcont : Continuous κ :=
    IsExpLieAlgebra.IsTestFunction.continuous (isExpLieAlgebra K n) ⟨hκs, hκc⟩
  have rep : ∀ g y, archSlice φ.1 g y = ∫ z, archSlice φ.1 g (y * z) * κ z ∂μ :=
    fun g y => hκ _ (hP g) y
  have repφ : ∀ g, φ.1 g = ∫ z, φ.1 (g * infEmb K n z) * κ z ∂μ := by
    intro g
    have := rep g 1
    simpa [archSlice_apply] using this
  have hc : Continuous φ.1 := hφ.continuous
  have hct := UpperTheory.constantTerm_convolution_arch K n r μ φ.1 φ.1 κ hc hκcont hκc repφ
  have hctc := UpperTheory.continuous_constantTerm K n r φ.1 hc
  have hsliceC : ∀ g, Continuous (archSlice (constantTerm r φ.1) g) := by
    intro g
    show Continuous fun x => constantTerm r φ.1 (g * infEmb K n x)
    exact hctc.comp (continuous_const.mul continuous_infEmb)
  have repct : ∀ g y, archSlice (constantTerm r φ.1) g y
      = ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := by
    intro g y
    simp only [archSlice_apply]
    rw [hct (g * infEmb K n y)]
    simp [mul_assoc, map_mul]
  have hs : IsArchSmooth (constantTerm r φ.1) := by
    intro g
    have hfun : archSlice (constantTerm r φ.1) g
        = fun y => ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := funext (repct g)
    rw [hfun]
    exact (isExpLieAlgebra K n).isSmoothFun_integral_mul μ (hsliceC g) ⟨hκs, hκc⟩
  refine ⟨hs, fun X => ?_⟩
  funext g
  have hD := (isExpLieAlgebra K n).continuous_convDeriv hκs ((isExpLieAlgebra K n).ofLie X)
  have hDc := (isExpLieAlgebra K n).hasCompactSupport_convDeriv hκc ((isExpLieAlgebra K n).ofLie X)
  have repU : ∀ h, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 h
      = ∫ y, φ.1 (h * infEmb K n y)
          * (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
    intro h
    rw [uAction_ι_apply,
      IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (φ.2 h) (rep h)]
    simp [archSlice_apply]
  rw [uAction_ι_apply,
    IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (hs g) (repct g),
    UpperTheory.constantTerm_convolution_arch K n r μ φ.1 _ _ hc hD hDc repU g]
  simp [archSlice_apply]
end
