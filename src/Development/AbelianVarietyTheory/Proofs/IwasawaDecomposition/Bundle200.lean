module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
public import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle196
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Core

variable {K V M : Type} [Field K] {σ : K →+* ℂ} [AddCommGroup V] [Module K V]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]


omit [FiniteDimensional ℂ M] in
theorem inner_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) (x y : M) : inner ℂ (f x) (f y) = (n : ℂ) * inner ℂ x y := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have h1 : ∀ x, ‖((((Real.sqrt n)⁻¹ : ℝ) : ℂ) • f) x‖ = ‖x‖ := by
    intro x
    have h2 : ‖f x‖ = Real.sqrt n * ‖x‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), h, mul_pow, Real.sq_sqrt hn.le]
    rw [LinearMap.smul_apply, norm_smul, h2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  have h3 := (LinearMap.norm_map_iff_inner_map_map _).1 h1 x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hn.le] at h3
  rw [← h3, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne']
  simp

omit [FiniteDimensional ℂ M] in
theorem inj_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) : Function.Injective f := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have := h x
  rw [hx, norm_zero] at this
  have h2 : ‖x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 (show n * ‖x‖ ^ 2 = 0 by rw [← this]; simp) with h | h
    · exact absurd h hn.ne'
    · exact h
  simpa using h2

end Core

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : hform H x y = star x ⬝ᵥ H *ᵥ y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mulVec {n a b : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin a) K) (E' : Matrix (Fin n) (Fin b) K)
    (x : Fin a → K) (y : Fin b → K) : hform H (E *ᵥ x) (E' *ᵥ y) = star x ⬝ᵥ (Eᴴ * H * E') *ᵥ y := by
  rw [hform_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem hform_orth {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K}
    (h : IsOrthProj H E Pr) (z : Fin d → K) (x : Fin n → K) : hform H (E *ᵥ z) (E *ᵥ (Pr *ᵥ x)) = hform H (E *ᵥ z) x := by
  have h1 := hform_mulVec H E (1 - E * Pr) z x
  rw [h.2, Matrix.zero_mulVec, dotProduct_zero, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, sub_eq_zero,
    ← Matrix.mulVec_mulVec] at h1
  exact h1.symm

variable (S : CSD K) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

theorem csum_hform (x y : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm x : S.Forms) (S.basis.equivFun.symm y : S.Forms) = hform S.H x y :=
  (S.isClassSum x y).symm

theorem act_coord (t : G) (x : Fin S.dim → K) :
    r t (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.actMat r t *ᵥ x) :=
  Subtype.ext (S.I_actMat r t x).symm

theorem gaOp_coord (a : MonoidAlgebra K G) (x : Fin S.dim → K) :
    S.gaOp r a (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.gaMat r a *ᵥ x) := by

  simp only [CSD.gaOp, CSD.gaMat, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, map_sum,
  map_smul, act_coord]

def lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : (Fin (S.lvlDim r P ψ) → K) →ₗ[K] S.Forms :=
  (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms) ∘ₗ (S.lvlE r P ψ).mulVecLin

theorem lvlForm_apply (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    lvlForm S r P ψ x = S.basis.equivFun.symm (S.lvlE r P ψ *ᵥ x) := rfl

theorem lvlForm_injective (P : Subgroup G) (ψ : P →* Kˣ) : Function.Injective (lvlForm S r P ψ) :=
  S.basis.equivFun.symm.injective.comp (image_idempotent_spec K _ _).1

theorem range_lvlE (P : Subgroup G) (ψ : P →* Kˣ) : LinearMap.range (S.lvlE r P ψ).mulVecLin = S.lvlPart r P ψ :=
  (image_idempotent_spec K _ _).2.trans (level_part_spec K S G r P ψ)

theorem range_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : Set.range (lvlForm S r P ψ) = lvlForms S r P ψ := by
  ext f
  obtain ⟨u, rfl⟩ := S.basis.equivFun.symm.surjective f
  have key : S.basis.equivFun.symm u ∈ lvlForms S r P ψ ↔ u ∈ S.lvlPart r P ψ := by
    refine forall_congr' fun h => ?_
    rw [act_coord, ← map_smul, S.basis.equivFun.symm.injective.eq_iff]
  rw [key, ← range_lvlE]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, S.basis.equivFun.symm.injective hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem csum_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) (x y : Fin (S.lvlDim r P ψ) → K) :
    S.csum (lvlForm S r P ψ x) (lvlForm S r P ψ y) = (Nat.card P : K) * hform (S.lvlH r P ψ) x y := by
  have hc : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  rw [lvlForm_apply, lvlForm_apply, csum_hform, hform_mulVec, hform_dot, CSD.lvlH, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rfl

theorem mem_lvlNab (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    x ∈ S.lvlNab r P ψ ↔ lvlForm S r P ψ x ∈ intForms S := by
  unfold CSD.lvlNab CSD.cutNab CSD.nabLat
  rw [exponent_index_lattice.mem_cutLat, mem_valLatF]
  rfl

end Coord

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lvlE_lvlOp (h : BlockHyp B ℓ v0 s) (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x) =
      B.S.gaMat B.r (idemOf ℓ.X) *ᵥ (B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ x) := by
  have hc := (idempotent_spec K v0 h.conj G ℓ.X h.irr).2 (lvlIdem ℓ.P ℓ.ψ)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ _ hc.symm).1]

theorem lvlE_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.lE ℓ Z *ᵥ z) = B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, BlockDat.lf_lvlE_lE h]
  rfl

theorem lvlForm_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    lvlForm B.S B.r ℓ.P ℓ.ψ (B.lE ℓ Z *ᵥ z) = B.toF ℓ Z z := by
  rw [lvlForm_apply, lvlE_lE h]
  rfl

theorem range_vE (h : BlockHyp B ℓ v0 s) : LinearMap.range (B.vE ℓ).mulVecLin =
    LinearMap.range (B.S.gaMat B.r (idemOf ℓ.X)).mulVecLin ⊓ B.S.lvlPart B.r ℓ.P ℓ.ψ :=
  good_part_spec K B.S G B.r ℓ.X h.irr ℓ.P ℓ.ψ

theorem lvlOp_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ (B.lE ℓ Z *ᵥ z) = B.lE ℓ Z *ᵥ z := by
  apply BlockDat.lf_lvlE_inj
  show B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _ = B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _
  rw [lvlE_lvlOp h, lvlE_lE h]
  have hm : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
  rw [range_vE h] at hm
  obtain ⟨⟨u, hu⟩, -⟩ := hm
  rw [← hu, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← (group_action_matrix_hom K B.S G B.r).2,
    (idempotent_spec K v0 h.conj G ℓ.X h.irr).1.idem]

theorem span_range_mulVec {σ : K →+* ℂ} {M : Type} [AddCommGroup M] [Module ℂ M] {n d : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (E : Matrix (Fin n) (Fin d) K) :
    Submodule.span ℂ (J '' Set.range fun z => E *ᵥ z) = Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    have hz : z = ∑ k, z k • (Pi.single k 1 : Fin d → K) := by
      ext i; simp [Pi.single_apply]
    rw [SetLike.mem_coe]
    beta_reduce

    rw [hz, Matrix.mulVec_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Matrix.mulVec_smul, map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, rfl⟩

variable {σ : K →+* ℂ} {H M ML : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M] [AddCommGroup ML] [Module K ML]



end Block

end GlobalTheory.Mem.LiftForms

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)

namespace GlobalTheory.VB

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]

theorem IsProjCurve.bddAbove_subDegs_of_kernel (hC : IsProjCurve k C) {B Q : C.Modules}
    [IsFiniteQC Q] (p : B ⟶ Q) (hK : BddAbove (subDegs k (kernel p)))
    (hQ : BddAbove (subDegs k Q)) : BddAbove (subDegs k B) := by
  have := hC.isNoetherian
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hQ
  refine ⟨a + b, ?_⟩
  rintro _ ⟨G, i, hi, rfl⟩
  have := hi.mono
  have := hi.isFiniteQC
  let q : G ⟶ Q := i ≫ p
  have hKG : IsFiniteQC (kernel q) := .of_mono (kernel.ι q)
  have hm : Mono (Abelian.factorThruCoimage q) := inferInstance
  have hc : IsFiniteQC (cokernel (kernel.ι q)) := .of_mono (Abelian.factorThruCoimage q)
  let j : kernel q ⟶ kernel p := kernel.lift p (kernel.ι q ≫ i) (by
    rw [Category.assoc]; exact kernel.condition q)
  have hj : Mono j := mono_of_mono_fac (kernel.lift_ι p (kernel.ι q ≫ i) _)
  have h₁ : deg k (kernel q) ≤ a := ha (IsCohSub.deg_mem (i := j) ⟨hj, hKG⟩)
  have h₂ : deg k (cokernel (kernel.ι q)) ≤ b :=
    hb (IsCohSub.deg_mem (i := Abelian.factorThruCoimage q) ⟨hm, hc⟩)
  rw [hC.deg_cokernel] at h₂
  omega

theorem IsProjCurve.bddAbove_subDegs_of_jointly_mono (hC : IsProjCurve k C) {D : C.Modules}
    [IsFiniteQC D] (hD : BddAbove (subDegs k D)) (n : ℕ) :
    ∀ (Z : C.Modules) [IsFiniteQC Z] (ψ : Fin n → (Z ⟶ D)),
      (∀ (W : C.Modules) (g : W ⟶ Z), (∀ j, g ≫ ψ j = 0) → g = 0) →
      BddAbove (subDegs k Z) := by
  have := hC.isNoetherian
  induction n with
  | zero =>
    intro Z _ ψ h
    have hZ : IsZero Z := (IsZero.iff_id_eq_zero Z).2 (h Z (𝟙 Z) fun j => j.elim0)
    refine ⟨0, ?_⟩
    rintro _ ⟨G, i, hi, rfl⟩
    have := hi.mono
    exact (deg_eq_zero_of_isZero k (hZ.of_mono i)).le
  | succ n ih =>
    intro Z _ ψ h
    have : IsFiniteQC (kernel (ψ 0)) := .of_mono (kernel.ι (ψ 0))
    refine hC.bddAbove_subDegs_of_kernel (ψ 0)
      (ih (kernel (ψ 0)) (fun j => kernel.ι (ψ 0) ≫ ψ j.succ) fun W g hg => ?_) hD
    have h0 : g ≫ kernel.ι (ψ 0) = 0 := h W _ fun j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [Category.assoc, kernel.condition, comp_zero]
      · rw [Category.assoc]; exact hg j
    exact (cancel_mono (kernel.ι (ψ 0))).1 (h0.trans (zero_comp).symm)

theorem dualMap_sum {F G : C.Modules} {ι : Type} (s : Finset ι) (f : ι → (F ⟶ G)) :
    dualMap (∑ j ∈ s, f j) = ∑ j ∈ s, dualMap (f j) :=
  map_sum (AddMonoidHom.mk' (dualMap (F := F) (G := G)) dualMap_add) f s

theorem bddAbove_subDegs_of_isVB : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    [IsIntegral C], IsProjCurve k C → ∀ (F : C.Modules) (r : ℕ), IsVB F r →
    BddAbove (subDegs k F) := by
  intro k _ C _ _ hC F r hF
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  have := hF.isFiniteQC
  have := hF.dual.isFiniteQC
  obtain ⟨m, n, φ, hφ⟩ := (hA.eventually_exists_epi_sigma (dual F)).exists
  have hL := Twist.isLB_lbZPow hA.isLB (-m)
  have hT := isVB_toMod hL
  let T := GlobalTheory.LB.toMod (lbZPow A (-m))
  have hD : IsVB (dual T) 1 := hT.dual
  have := hD.isFiniteQC
  have := Abelian.hasFiniteBiproducts (C := C.Modules)
  let φ' : (⨁ fun _ : Fin n => T) ⟶ dual F := (biproduct.isoCoproduct _).hom ≫ φ
  have hφ' : Epi φ' := inferInstance
  have hb := hF.isIso_toBidual_of_local_frames
  refine hC.bddAbove_subDegs_of_jointly_mono (hC.isMaxSubDeg_of_rank_one hD).bddAbove n F
    (fun j => cartierDualToBidual F ≫ dualMap (biproduct.ι (fun _ : Fin n => T) j ≫ φ')) fun W g hg => ?_
  have h0 : (g ≫ cartierDualToBidual F) ≫ dualMap φ' = 0 := by
    rw [← Category.comp_id ((g ≫ cartierDualToBidual F) ≫ dualMap φ'), ← dualMap_id,
      ← biproduct.total, dualMap_sum, Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hg j
    rw [dualMap_comp, dualMap_comp] at *
    simp only [Category.assoc] at *
    rw [reassoc_of% this, zero_comp]
  have h1 : g ≫ cartierDualToBidual F = 0 := (cancel_mono (dualMap φ')).1 (h0.trans zero_comp.symm)
  exact (cancel_mono (cartierDualToBidual F)).1 (h1.trans zero_comp.symm)

end GlobalTheory.VB
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatEigArith

theorem esymm_map_mul_const' (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (· * c)).esymm k = c ^ k * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def]
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    (Multiset.mem_powersetCard.1 ht).2, Multiset.map_id', mul_comm]

theorem exponent_eq (q n k : ℕ) (hq : 0 < q) (hk : k ≤ n) :
    (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (k * (n - 1)))⁻¹ * (q : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) =
      ((q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) ^ k := by
  have hQ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp
  have h2 : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    have h0 := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
    have e : ((k * (k - 1) / 2 * 2 : ℕ) : ℂ) = ((k * (k - 1) : ℕ) : ℂ) := by rw [h0]
    simp only [Nat.cast_mul, Nat.cast_ofNat] at e
    rw [eq_div_iff two_ne_zero, e, Nat.cast_sub (show 1 ≤ k from hk1)]
    push_cast
    ring
  have h3 : ((k * (n - 1) : ℕ) : ℂ) = (k : ℂ) * ((n : ℂ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  rw [← Complex.cpow_natCast, ← Complex.cpow_natCast, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hQ,
    ← Complex.cpow_add _ _ hQ, ← Complex.cpow_mul_nat, h2, h3]
  congr 1
  push_cast
  ring

theorem satEig_inv_normalised : ∀ (q n k : ℕ), 0 < q → k ≤ n → ∀ (α : Fin n → ℂˣ),
    (q : ℂ) ^ (k * (k - 1) / 2) * (((q : ℂ) ^ (k * (n - 1)))⁻¹ *
        GlobalTheory.LFun.satEig q n ((Finset.univ.val.map α).map (·⁻¹)) k) =
      ((Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * (q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))).esymm k := by
  intro q n k hq hk α
  rw [esymm_map_mul_const', GlobalTheory.LFun.satEig, ← mul_assoc, ← mul_assoc, exponent_eq q n k hq hk]
  congr 2
  simp [Multiset.map_map, Function.comp_def, Units.val_inv_eq_inv_val]

end GlobalTheory.SatEigArith
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Classical

theorem _root_.GlobalTheory.T.doubleCoset_reps_conjugate_level_groups : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (cst' : LocCst X (rowSG Pr sel mu')) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → cst.sharp = true → cst'.sharp = true → L.Ok Ch sel mu cst G m2 → L'.Ok Ch sel mu' cst' G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (b' : L'.β j) (w : {w // w ∈ Pr.vGs}) (r κ : AutY X R j), r ∈ Loc.R1 X.E (R.N j) (cOf R j) → κ ∈ Jat (Pr := Pr) true j w.1 → L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ → ∃ x : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), (r = 1 → x = 1) ∧ (∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), hbar ∈ (L.levG j b w).H ↔ x * hbar * x⁻¹ ∈ (L'.levG j b' w).H) ∧ ∀ (hbar : ↥(L.levG j b w).H) (hbar' : ↥(L'.levG j b' w).H), hbar'.1 = x * hbar.1 * x⁻¹ → (L.levG j b w).lam hbar = (L'.levG j b' w).lam hbar' := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match | exact GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match | (intros; apply GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.upwardOperator_preserves_rationality : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), (∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x) → ∀ (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V), LT.Uop D u 0 v ((D.fm u).emb 0 x) ∈ (D.fm u).Fi 0 → ∃ y, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x) := by
  first | exact @GlobalTheory.LevelHecke.uop_rat | exact GlobalTheory.LevelHecke.uop_rat | (intros; apply GlobalTheory.LevelHecke.uop_rat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u) (v : HeightOneSpectrum (𝓞 D.host.F)) (_ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal)
    (a : v.adicCompletionIntegers D.host.F) (_ : Valued.v (a : v.adicCompletion D.host.F) < 1),
    ∃ b : v.adicCompletionIntegers D.host.F, a = (((D.mem u).A.T : ℕ) : v.adicCompletionIntegers D.host.F) * b := by
  first | exact @GlobalTheory.LevelUnif.dvd_of_val_lt_one | exact GlobalTheory.LevelUnif.dvd_of_val_lt_one | (intros; apply GlobalTheory.LevelUnif.dvd_of_val_lt_one <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.typeAndTwistPlaces_over_other_than_split : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.v ∉ gPl D → s.w ∈ L.Q t → (∀ PP ∈ L.Pg, ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) ∧ (∀ PP ∈ L.Q t, PP ≠ s.w → ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) := by
  first | exact @GlobalTheory.OtherPlaces.over_ne | exact GlobalTheory.OtherPlaces.over_ne | (intros; apply GlobalTheory.OtherPlaces.over_ne <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A)
    (v : ∀ e : ℕ, LB.Iso ((LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2)).pull (fstG I e P'.A).left)
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull ((β e).hom.left ≫ (fstG I e P.A).left))),
    (∀ e, (v e).IsGen) →
    (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) →
    (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
      (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z (fun _ => j) (fun _ => fun _ => j') =
        gw (v e) r z (fun _ => j) (fun _ => fun _ => j')) →
    ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso (LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2))
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen ∧
    ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
        (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
        gw w (r ≫ (fstG I e P'.A).left) z (fun _ => j) (fun _ => j') = gw (v e) r z (fun _ => j) (fun _ => fun _ => j') := by
  first | exact @GlobalTheory.exists_iso_of_compatible_thickenings_sq | exact GlobalTheory.exists_iso_of_compatible_thickenings_sq | (intros; apply GlobalTheory.exists_iso_of_compatible_thickenings_sq <;> assumption)
end
