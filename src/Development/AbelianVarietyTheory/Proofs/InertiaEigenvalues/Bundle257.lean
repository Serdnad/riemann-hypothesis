module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle030
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle034
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle040
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle234
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Formalism.CoboundaryTransfers.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Mathlib.RingTheory.DedekindDomain.Basic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

section TwistDeRham

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem deRhamTwist_galoisAct_period (g : G) :
    PD.actdR g (PD.ι PD.t) = ((PD.χ g : Qpˣ) : Qp) • PD.ι PD.t := by
  rw [← PD.ι_comm, PD.t_act, ← algebraMap_smul K₀ ((PD.χ g : Qpˣ) : Qp) PD.t, map_smul,
    algebraMap_smul]

theorem drTwist_pow_mem (e : ℕ) : (PD.ι PD.t) ^ e ∈ PD.Fil (e : ℤ) := by
  induction e with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact_mod_cast PD.Fil_mul _ _ _ _ ih PD.mem_filtration_one

theorem drTwist_Fil_le (e : ℕ) : PD.Fil (e : ℤ) ≤ PD.Fil 0 := by
  induction e with
  | zero => simp
  | succ n ih =>
    refine le_trans ?_ ih
    exact_mod_cast PD.Fil_anti (n : ℤ)

noncomputable def drTwistMap (e : ℕ) : K →ₗ[Qp] BdR :=
  (LinearMap.mulRight Qp ((PD.ι PD.t) ^ e)) ∘ₗ (IsScalarTower.toAlgHom Qp K BdR).toLinearMap

theorem drTwistMap_apply (e : ℕ) (k : K) :
    drTwistMap PD e k = algebraMap K BdR k * (PD.ι PD.t) ^ e := rfl

theorem drTwistMap_injective (e : ℕ) : Function.Injective (drTwistMap PD e) := by
  have hnt : Nontrivial BdR := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact PD.not_mem_filtration_two (by rw [Subsingleton.elim (PD.ι PD.t) 0]; exact Submodule.zero_mem _)
  intro a b hab
  rw [drTwistMap_apply, drTwistMap_apply] at hab
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  exact (algebraMap K BdR).injective (hu.mul_right_cancel hab)

theorem drTwistMap_mem (e : ℕ) (k : K) : drTwistMap PD e k ∈ PD.Fil 0 := by
  rw [drTwistMap_apply, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (drTwist_Fil_le PD e (drTwist_pow_mem PD e))

theorem drTwist_act_pow (e : ℕ) (g : G) :
    PD.actdR g ((PD.ι PD.t) ^ e) = ((PD.χ g : Qpˣ) : Qp) ^ e • (PD.ι PD.t) ^ e := by
  rw [map_pow, deRhamTwist_galoisAct_period, smul_pow]

theorem drTwistMap_fixed (e : ℕ) (g : G) (k : K) :
    (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (drTwistMap PD e k) = drTwistMap PD e k := by
  rw [drTwistMap_apply, map_mul, AlgEquiv.commutes, drTwist_act_pow, mul_smul_comm, smul_smul,
    ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul]

theorem drTwistMap_range (e : ℕ) (y : BdR)
    (hy : ∀ g, (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y = y) :
    ∃ k, drTwistMap PD e k = y := by
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  obtain ⟨z, hz⟩ := hu.exists_left_inv
  have hyz : y = (y * z) * (PD.ι PD.t) ^ e := by rw [mul_assoc, hz, mul_one]
  obtain ⟨k, hk⟩ := PD.invdR (y * z) (fun g => by
    apply hu.mul_right_cancel
    have h := hy g
    rw [hyz, map_mul, drTwist_act_pow, mul_smul_comm, smul_smul,
      ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul] at h
    exact h)
  exact ⟨k, by rw [drTwistMap_apply, hk, ← hyz]⟩

variable {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V)

theorem drTwist_act_tmul (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) (g : G) (v : V) (y : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] y) =
      v ⊗ₜ[Qp] ((((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y) := by
  have : actVdR PD ρ g (v ⊗ₜ[Qp] y) = ρ g v ⊗ₜ[Qp] PD.actdR g y := rfl
  rw [this, h, ← map_inv₀, ← map_pow, algebraMap_smul, smul_tmul]

theorem drTwist_range (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) :
    LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) =
      DdR PD ρ := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | tmul v k =>
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, AlgebraTensorModule.map_tmul, sub_eq_zero]
      intro g
      rw [drTwist_act_tmul PD ρ e h, drTwistMap_fixed]
  · intro x hx
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hx
    let b := Module.Basis.ofVectorSpace Qp V
    let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) b
    have hE : ∀ g (x : V ⊗[Qp] BdR) i, E (actVdR PD ρ g x) i =
        (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (E x i) := by
      intro g x i
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb, smul_add]
      | tmul v y =>
        rw [drTwist_act_tmul PD ρ e h]
        simp only [E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
        rw [← algebraMap_smul K (b.repr v i) y, map_smul, algebraMap_smul, smul_comm]
    have hx' : x = E.symm (E x) := (E.symm_apply_apply x).symm
    rw [hx', TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    obtain ⟨k, hk⟩ := drTwistMap_range PD e (E x i) (fun g => by rw [← hE, hx g])
    exact ⟨b i ⊗ₜ k, by rw [AlgebraTensorModule.map_tmul, hk]; rfl⟩

end TwistDeRham

theorem isDR_and_DdR_le_Fil_zero_of_twist : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) (e : ℕ), (∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) → IsDR PD ρ ∧ DdR PD ρ ≤ FilV PD (LL := LL) (V := V) 0 := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ _ ρ e h
  have hr := drTwist_range PD ρ e h
  constructor
  · have hinj : Function.Injective
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ (drTwistMap_injective PD e)
    have := PD.finK
    unfold IsDR
    rw [← hr, LinearMap.finrank_range_of_inj hinj, Module.finrank_tensorProduct, mul_comm]
  · rw [← hr]
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | tmul v k => exact ⟨v ⊗ₜ ⟨drTwistMap PD e k, drTwistMap_mem PD e k⟩, rfl⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem isInternal_map_of_corner {K : Type} [Field K] {n t : ℕ} (ι : Type) [Fintype ι]
    [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hV : DirectSum.IsInternal Vs) (hba : b * a = 1)
    (he : ∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) :
    DirectSum.IsInternal (fun j => (Vs j).map b.mulVecLin) := by
  classical
  have hfg : ∀ w : Fin t → K, b.mulVecLin (a.mulVecLin w) = w := fun w => by
    simp [Matrix.mulVec_mulVec, hba]
  have hE : (a * b).mulVecLin = a.mulVecLin ∘ₗ b.mulVecLin := Matrix.mulVecLin_mul a b

  have hback : ∀ S : Submodule K (Fin n → K), S.map (a * b).mulVecLin ≤ S →
      (S.map b.mulVecLin).map a.mulVecLin ≤ S := by
    intro S hS
    rwa [← Submodule.map_comp, ← hE]
  have hVj : ∀ j, (Vs j).map (a * b).mulVecLin ≤ Vs j := by
    rintro j _ ⟨v, hv, rfl⟩
    exact he j v hv
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hV ⊢
  obtain ⟨hind, htop⟩ := hV
  constructor
  · rw [iSupIndep_def] at hind ⊢
    intro j
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hrest : (⨆ k, ⨆ (_ : k ≠ j), Vs k).map (a * b).mulVecLin ≤ ⨆ k, ⨆ (_ : k ≠ j), Vs k := by
      simp_rw [Submodule.map_iSup]
      exact iSup₂_mono fun k _ => hVj k
    have hx2' : x ∈ (⨆ k, ⨆ (_ : k ≠ j), Vs k).map b.mulVecLin := by
      simp_rw [Submodule.map_iSup]
      exact hx2
    have h1 : a.mulVecLin x ∈ Vs j := hback _ (hVj j) (Submodule.mem_map_of_mem hx1)
    have h2 : a.mulVecLin x ∈ ⨆ k, ⨆ (_ : k ≠ j), Vs k :=
      hback _ hrest (Submodule.mem_map_of_mem hx2')
    rw [← hfg x, Submodule.disjoint_def.1 (hind j) _ h1 h2, map_zero]
  · rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
    exact fun w => ⟨a.mulVecLin w, hfg w⟩

theorem exists_separable_charpoly_of_isInternal {K : Type} [Field K] [Infinite K] {t : ℕ}
    (ι : Type) [Fintype ι] [DecidableEq ι] (W : ι → Submodule K (Fin t → K))
    (hW : DirectSum.IsInternal W) :
    ∃ D : Matrix (Fin t) (Fin t) K, (∀ j, ∀ w ∈ W j, D.mulVec w ∈ W j) ∧
      D.charpoly.Separable := by
  classical

  let v : ∀ j, Module.Basis (Fin (Module.finrank K (W j))) K (W j) := fun j => Module.finBasis K (W j)
  let B := hW.collectedBasis v
  let μ : (Σ j, Fin (Module.finrank K (W j))) → K :=
    fun s => Infinite.natEmbedding K (Fintype.equivFin _ s)
  have hμ : Function.Injective μ :=
    (Infinite.natEmbedding K).injective.comp (Fin.val_injective.comp (Fintype.equivFin _).injective)
  let φ : (Fin t → K) →ₗ[K] (Fin t → K) := B.constr K (fun s => μ s • B s)
  have hφB : ∀ s, φ (B s) = μ s • B s := fun s => B.constr_basis K _ s
  refine ⟨LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro j w hw
    have hD : (LinearMap.toMatrix' φ).mulVec w = φ w := by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    have hw' : w = ((∑ k, (v j).repr ⟨w, hw⟩ k • v j k : W j) : Fin t → K) := by
      rw [(v j).sum_repr]

    rw [hD, hw', Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Submodule.coe_smul, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have hk : ((v j k : W j) : Fin t → K) = B ⟨j, k⟩ := by simp [B]
    rw [hk, hφB]
    exact Submodule.smul_mem _ _ (hW.collectedBasis_mem v ⟨j, k⟩)
  · have h1 : (LinearMap.toMatrix' φ).charpoly = φ.charpoly := by
      rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]
    have h2 : LinearMap.toMatrix B B φ = Matrix.diagonal μ := by
      ext s s'
      rw [LinearMap.toMatrix_apply, hφB, map_smul, B.repr_self, Matrix.diagonal_apply]
      by_cases h : s = s'
      · subst h; simp
      · simp [h]
    rw [h1, ← LinearMap.charpoly_toMatrix φ B, h2, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.2 hμ

theorem exists_corner_separable_charpoly :
    ∀ {K : Type} [Field K] [Infinite K] {n t : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), DirectSum.IsInternal Vs → b * a = 1 → (∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) → ∃ m : Matrix (Fin n) (Fin n) K, (∀ j, ∀ v ∈ Vs j, m.mulVec v ∈ Vs j) ∧ (b * m * a).charpoly.Separable := by
  intro K _ _ n t ι _ _ Vs a b hV hba he
  obtain ⟨D, hD, hsep⟩ :=
    exists_separable_charpoly_of_isInternal ι _ (isInternal_map_of_corner ι Vs a b hV hba he)
  refine ⟨a * D * b, ?_, ?_⟩
  · intro j v hv
    obtain ⟨u, hu, hu'⟩ := hD j (b.mulVec v) (Submodule.mem_map_of_mem hv)
    have hm : (a * D * b).mulVec v = (a * b).mulVec u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      congr 1
      exact hu'.symm
    rw [hm]
    exact he j u hu
  · have hc : b * (a * D * b) * a = D := by
      calc b * (a * D * b) * a = (b * a) * D * (b * a) := by simp only [Matrix.mul_assoc]
        _ = D := by rw [hba, Matrix.one_mul, Matrix.mul_one]
    rw [hc]
    exact hsep

end GlobalTheory.SpanRing
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_mem_submodule_all_charpoly_separable : ∀ {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ) (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K), (∀ x, (a x).charpoly.Separable ∨ ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) → ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  first | exact @GlobalTheory.SepGeneric.exists_separable | exact GlobalTheory.SepGeneric.exists_separable | (intros; apply GlobalTheory.SepGeneric.exists_separable <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BaseChangeConj

open Formalism.MainNotions.SumRepresentations Polynomial

theorem charpoly_eq_of_dense' {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : Type} [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [Infinite k] {a : ℕ} (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

end GlobalTheory.BaseChangeConj
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem _root_.GlobalTheory.rank_eq_of_acts_through_first_block {K : Type} [Field K] {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K)
    (ε : Matrix (Fin r) (Fin r) K) (h : ∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) :
    F.rank = ε.rank := by
  have key : (LinearMap.range F.mulVecLin).map (e : (Fin n → K) →ₗ[K] _) =
      (LinearMap.range ε.mulVecLin).map (LinearMap.inl K (Fin r → K) (Fin t → K)) := by
    ext ⟨a, b⟩
    simp only [Submodule.mem_map, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, hx⟩
      rw [LinearEquiv.coe_coe, h] at hx
      exact ⟨_, ⟨(e u).1, rfl⟩, by simpa using hx⟩
    · rintro ⟨_, ⟨v, rfl⟩, hx⟩
      refine ⟨_, ⟨e.symm (v, 0), rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, h]
      simpa using hx
  simp only [← Matrix.finrank_range_mulVecLin]
  rw [← LinearEquiv.finrank_map_eq e, key]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective _).finrank_eq.symm

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.rank_map_ringHom : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K), (M.map φ).rank = M.rank := by
  first | exact @GlobalTheory.matrix_rank_map_field | exact GlobalTheory.matrix_rank_map_field | (intros; apply GlobalTheory.matrix_rank_map_field <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.LenUnitPow

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]


variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem _root_.GlobalTheory.LenUnitPow.natCast_ne_zero : (l : O) ≠ 0 := by
  intro h
  have hker : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := by
    refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
    intro hbot
    have hl : ((l : ℤ_[l])) ∈ RingHom.ker (algebraMap ℤ_[l] O) := by
      rw [RingHom.mem_ker, map_natCast]; exact h
    rw [hbot, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  have hbot : (⊥ : Ideal O).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) (⊥ : Ideal O) ?_
    change (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal
    rwa [← RingHom.ker_eq_comap_bot]
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm


variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem _root_.GlobalTheory.LenUnitPow.natCast_not_isUnit : ¬ IsUnit (l : O) := by
  intro h
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal O)
  have hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O) := by
    rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hl
  exact hl h

end GlobalTheory.LenUnitPow
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_idempotent_sub_mem_of_pow_sub_mem' : ∀ (l : ℕ) [Fact l.Prime] {R : Type} [Ring R] [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R] (b : R), ∃ E : R, E * E = E ∧ ∀ (M : Submodule ℤ_[l] R) (c : R), (∀ n : ℕ, b ^ (n + 1) - c ∈ M) → E - c ∈ M := by
  first | exact @GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem | exact GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem | (intros; apply GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' : ∀ (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ), 1 ≤ m → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m → ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m → ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  first | exact @GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level | exact GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level | (intros; apply GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

theorem _root_.GlobalTheory.T.continuous_cyclotomic_character_localGalois : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → Continuous (fun g : G => ((ε g : Oˣ) : O)) := by
  first | exact @GlobalTheory.FunctorialityH2.cyc_char_continuous | exact GlobalTheory.FunctorialityH2.cyc_char_continuous | (intros; apply GlobalTheory.FunctorialityH2.cyc_char_continuous <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

theorem _root_.GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ, DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  first | exact @GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | exact GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | (intros; apply GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

theorem _root_.GlobalTheory.T.padicInt_ringHom_continuous_of_padicCoeff' : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  first | exact @GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff | exact GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff | (intros; apply GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff <;> assumption)
end
