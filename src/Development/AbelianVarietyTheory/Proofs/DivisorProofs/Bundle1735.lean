module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheaf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.LatMove

open scoped Matrix

theorem mem_hat_stdLat_iff {D : D7} {n : ℕ} (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E n : Set (Fin n → D.host.E)) ↔ IntVec z := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, r, congrArg (fun t => a ⊗ₜ[D.host.F] t) hr.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [Submodule.mem_one.2 ⟨x, rfl⟩, zero_mem _]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

theorem mem_hat_colLat_iff {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E)
    (w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) ↔
      IntVec (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) := by
  have ew : GlobalTheory.UnRep.fm D.host.F B.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.HatPullback.fm_mul', Units.mul_inv, GlobalTheory.HatPullback.fm_one', Matrix.one_mulVec]
  have h1 := GlobalTheory.HatPullback.main D.host.F D.host.E n B (Formalism.L2.DIV.colLat B) (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w)
  rw [ew, GlobalTheory.ColStd.colLat_comap_eq_stdLat] at h1
  exact h1.trans (mem_hat_stdLat_iff _)

theorem swap_mem_hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (u i)) ∈ Formalism.L2.Herm.hatL (F := F) L ↔
      u ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  rw [GlobalTheory.GenusTranslate.hatL_iff]
  simp only [AlgEquiv.symm_apply_apply]

theorem exists_move {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) :
    ∃ x ∈ GfC V, ∀ w, w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin V.rank → D.host.E)) ↔
      (finHom V x).1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨x, hx, h⟩ := GlobalTheory.GenusTranslate.exists_move_colLat D V B _ hB (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)
  refine ⟨x, hx, fun w => ?_⟩
  have h1 := h fun i => Formalism.IndefR.Lev.swapAE D (w i)
  have h2 : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (w i)) =
      fun i => Formalism.IndefR.Lev.swapAE D (((finHom V x).1 *ᵥ w) i) :=
    funext fun i => (RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) (finHom V x).1 w i).symm
  rw [h2] at h1
  exact (swap_mem_hatL_iff _ w).symm.trans (h1.trans (swap_mem_hatL_iff _ ((finHom V x).1 *ᵥ w)))

theorem exists_finite_point : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  intro D _ V M hM
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse hM)
  obtain ⟨B, rfl⟩ := hu
  obtain ⟨x, hx, h⟩ := exists_move V B hM
  refine ⟨x⁻¹, inv_mem hx, fun y => ?_⟩
  have hL : L0c D V = (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) :=
    Set.ext fun z => (GlobalTheory.PlaceModel.mem_latFrame V z).symm
  have h1 := h ((finHom V x⁻¹).1 *ᵥ y)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec,
    mem_hat_colLat_iff, Matrix.coe_units_inv] at h1
  rw [hL]
  exact h1.symm

end GlobalTheory.DefTransfer.LatMove
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.equiv_of_stalkwise_base_change : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F := by
  first
  | exact @GlobalTheory.EtC.LocGlobSp.main
  | exact GlobalTheory.EtC.LocGlobSp.main
  | (intros; apply GlobalTheory.EtC.LocGlobSp.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.DivAssembly

section Ring

variable {R : Type*} [CommRing R] {a b : R}

theorem nrm_one' : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

theorem nrm_star' (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by simp [nrm]

theorem star_mul_eq' (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  have h := mul_star_eq (star x)
  rwa [star_star, nrm_star'] at h

theorem nrm_trunc (e : R) (he : e * e = e) (g : ℍ[R, a, b]) :
    nrm (e • (g - 1) + 1) = e * nrm g + (1 - e) := by
  simp only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub, QuaternionAlgebra.imJ_sub,
    QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one,
    QuaternionAlgebra.imK_one, smul_eq_mul]
  linear_combination ((g.re - 1) ^ 2 - a * g.imI ^ 2 - b * g.imJ ^ 2 + a * b * g.imK ^ 2) * he

end Ring

section Alg

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem prod_decomp (e : R) (he : e * e = e) (g : A) :
    ((1 - e) • (g - 1) + 1) * (e • (g - 1) + 1) = g := by
  have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, h0, zero_smul, zero_add]
  rw [← add_assoc, ← add_smul, show e + (1 - e) = 1 by ring, one_smul, sub_add_cancel]

end Alg

variable {F : Type} [Field F] [NumberField F]

theorem isPlacesIdem_idem {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h.1 w hw, one_mul]
    · rw [h.2.1 w hw, zero_mul]
  · refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV F u (sndA F (ε * ε)) = evalV F u (sndA F ε)
    rw [map_mul, map_mul]
    by_cases hu : u ∈ S₂
    · rw [h.2.2.1 u hu, one_mul]
    · rw [h.2.2.2 u hu, zero_mul]

theorem rat_mul' {a b : F} (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_one' {a b : F} : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem continuous_smul_const {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}
    (x : ℍ[R, a, b]) : Continuous fun t : R => t • x := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

end GlobalTheory.QSA.DivAssembly

namespace GlobalTheory.QSA.DivAssembly

variable {F : Type} [Field F] [NumberField F]

theorem conj_mem_normOneIdempotentSubgroup_of_rational_relation {a b : F} (ε : AF F) (w c c' : DA F a b) (l : AF F) (hl : IsUnit l) (δ γ : ℍ[F, a, b])
    (hδ : nrm δ ≠ 0) (hγ : nrm γ = 1) (h : DA F a b) (hh : nrm h = 1) (hhε : ε • (h - 1) = h - 1)
    (hcc' : c * c' = 1)
    (hyw : l • (rat δ * c) * w = rat γ * l • (rat δ * c) * h) : c * w * c' ∈ H0 ε := by
  set δ' : ℍ[F, a, b] := (nrm δ)⁻¹ • star δ with hδ'
  have hδδ : δ' * δ = 1 := by
    rw [hδ', smul_mul_assoc, star_mul_eq', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hδ, map_one]
  have E1 : rat δ * c * w = rat γ * rat δ * c * h := by
    have h2 : l • (rat δ * c * w) = l • (rat γ * rat δ * c * h) := by
      rw [← smul_mul_assoc, hyw, mul_smul_comm, smul_mul_assoc, mul_assoc (rat γ), mul_assoc (rat γ)]
      simp only [mul_assoc]
    exact hl.smul_left_cancel.1 h2
  refine ⟨δ' * γ * δ, ?_, c * h * c', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, hγ, mul_one, ← nrm_mul, hδδ, nrm_one']
  · rw [nrm_mul, nrm_mul, hh, mul_one, ← nrm_mul, hcc', nrm_one']
  · have e1 : c * h * c' - 1 = c * (h - 1) * c' := by
      rw [mul_sub, sub_mul, mul_one, hcc']
    rw [e1, ← smul_mul_assoc, ← mul_smul_comm, hhε]
  · calc c * w * c' = (rat δ' * rat δ) * c * w * c' := by rw [← rat_mul', hδδ, rat_one', one_mul]
      _ = rat δ' * (rat δ * c * w) * c' := by simp only [mul_assoc]
      _ = rat δ' * (rat γ * rat δ * c * h) * c' := by rw [E1]
      _ = rat (δ' * γ * δ) * (c * h * c') := by simp only [rat_mul', mul_assoc]

theorem strongApproximation_normOne_divisionQuaternion : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb hdiv S₁ S₂ ε hε hS hsurj g hg
  have hee : ε * ε = ε := isPlacesIdem_idem hε
  obtain ⟨hmul, -, -, -⟩ := GlobalTheory.T.closure_normOneProducts_h0_properties F a b ε hee
  obtain ⟨htr, -, -, hT2⟩ := GlobalTheory.T.quaternion_algebra_topological_ring (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b)
  haveI : IsTopologicalRing (DA F a b) := htr
  haveI : T2Space (AF F) := by
    haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
    haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
    exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  haveI : T2Space (DA F a b) := hT2 inferInstance
  obtain ⟨C, hC, hfuj⟩ := GlobalTheory.T.fujisaki_divisionQuaternionAlgebra_mod_centre F a b ha hb hdiv

  have key : ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F),
      IsPlacesIdem T₁ T₂ η → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
    intro T₁ T₂ η hη g hg hgη
    have hee' : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hee
    set gS : DA F a b := ε • (g - 1) + 1 with hgSdef
    set gN : DA F a b := (1 - ε) • (g - 1) + 1 with hgNdef
    have hprod : gN * gS = g := prod_decomp ε hee g
    have hgS : gS ∈ H0 (a := a) (b := b) ε := by
      refine ⟨1, nrm_one', gS, ?_, ?_, by rw [rat_one', one_mul]⟩
      · rw [hgSdef, nrm_trunc ε hee, hg]; ring
      · rw [hgSdef, add_sub_cancel_right, smul_smul, hee]
    have hgN1 : nrm gN = 1 := by rw [hgNdef, nrm_trunc (1 - ε) hee', hg]; ring
    have hgNε : ε • (gN - 1) = 0 := by
      rw [hgNdef, add_sub_cancel_right, smul_smul, show ε * (1 - ε) = 0 by linear_combination -hee, zero_smul]
    have hgNη : η • (gN - 1) = gN - 1 := by
      rw [hgNdef, add_sub_cancel_right, smul_comm, hgη]
    have hW : ∀ W ∈ 𝓝 gN, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ ∃ w ∈ W, c * w * c' ∈ H0 (a := a) (b := b) ε := by
      intro W hW
      obtain ⟨w, hwW, y, hy, γ, hγ, h, hh, hhε, hyw⟩ :=
        GlobalTheory.T.normOneQuaternion_near_conj_rational_times_supported F a b ha hb S₁ S₂ ε hε hS hsurj gN hgN1 hgNε W hW
      obtain ⟨δ, l, c, c', hδ, hl, hc, hc', hcc', hc'c, rfl⟩ := hfuj y hy
      exact ⟨c, hc, c', hc', hcc', hc'c, w, hwW, conj_mem_normOneIdempotentSubgroup_of_rational_relation ε w c c' l hl δ γ hδ hγ h hh hhε hcc' hyw⟩
    obtain ⟨c, -, c', -, hcc', hc'c, hmem⟩ := GlobalTheory.T.exists_conj_mem_closure_of_isCompact (DA F a b) (H0 (a := a) (b := b) ε) C hC gN hW
    have hgN := GlobalTheory.T.mem_closure_rationalNormOne_of_idempotent_conj F a b ha hb T₁ T₂ η hη ε hee gN hgN1 hgNη c c' hcc' hc'c hmem
    rw [← hprod]
    exact hmul _ hgN _ (subset_closure hgS)

  suffices g ∈ closure (closure (H0 (a := a) (b := b) ε)) by rwa [closure_closure] at this
  have hφ : Continuous fun η : AF F => η • (g - 1) + 1 := (continuous_smul_const (g - 1)).add continuous_const
  rw [mem_closure_iff_nhds]
  intro V hV
  have hpre : (fun η : AF F => η • (g - 1) + 1) ⁻¹' V ∈ 𝓝 (1 : AF F) :=
    hφ.continuousAt.preimage_mem_nhds (by rwa [one_smul, sub_add_cancel])
  obtain ⟨T₁, T₂, η, hη, hηV⟩ := GlobalTheory.T.exists_placesIdempotent_near_one_adeles F _ hpre
  have hηη : η * η = η := isPlacesIdem_idem hη
  refine ⟨η • (g - 1) + 1, hηV, key T₁ T₂ η hη _ ?_ ?_⟩
  · rw [nrm_trunc η hηη, hg]; ring
  · rw [add_sub_cancel_right, smul_smul, hηη]

end GlobalTheory.QSA.DivAssembly
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.homFixedPullbackRepresentable_glue_openCover : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (J : Type) (U : J → S.Opens), (∀ p : S, ∃ i, p ∈ U i) → (∀ i, ∃ (AU : Over (U i).toScheme) (_ : GrpObj AU) (BU : Over (U i).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U i).ι φA ∧ IsGrpPullback BU B (U i).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | exact @GlobalTheory.homFixRep_glue_opens | exact GlobalTheory.homFixRep_glue_opens | (intros; apply GlobalTheory.homFixRep_glue_opens <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.surjective_pi_liftKaehler_coordinateDerivations : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)), (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) → Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  first | exact @GlobalTheory.CechPer.surjective_pi_liftKaehler_coord | exact GlobalTheory.CechPer.surjective_pi_liftKaehler_coord | (intros; apply GlobalTheory.CechPer.surjective_pi_liftKaehler_coord <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isRegular_periodic_ratioCover_families : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (N : ℕ) (σ : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (σ k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), σ k (z + l) = σ k z) → (∀ k j, ∀ z ∈ pre u.ex (W k), z ∈ pre u.ex (W j) → σ k z = val u.ex _ (r k j) z ^ N * σ j z) → ∀ k, IsReg u.ex (W k) (σ k) := by
  first | exact @GlobalTheory.CechPer.ratio_periodic_isReg | exact GlobalTheory.CechPer.ratio_periodic_isReg | (intros; apply GlobalTheory.CechPer.ratio_periodic_isReg <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  first | exact @GlobalTheory.KSp.GaussMain.hasGauss_herm | exact GlobalTheory.KSp.GaussMain.hasGauss_herm | (intros; apply GlobalTheory.KSp.GaussMain.hasGauss_herm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.ExpLin

open GlobalTheory.TangentOrigin

theorem existsUnique_linear_lift :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
      SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)) (α : G ⟶ G),
      IsExp y e → IsExp y e' → IsMonHom α → ∃! M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (M z) = e z ≫ α := by
  intro X G _ _ g hab hsm y e e' α he he' hα
  obtain ⟨Λ, hdisc, -, hker⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice X G g hab hsm y e' he'
  letI : CommGroup (Over.mk y ⟶ G) := inferInstance
  let ex : (Fin g → ℂ) →+ Additive (Over.mk y ⟶ G) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (e' z)) he'.1
  let G' : (Fin g → ℂ) →+ Additive (Over.mk y ⟶ G) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (e z ≫ α)) (fun z w ↦ by
      show e (z + w) ≫ α = (e z ≫ α) * (e w ≫ α)
      rw [he.1]
      exact MonObj.mul_comp _ _ α)
  let pt : (Over.mk y).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (Over.mk y).left, q = pt := fun q ↦ Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (e' 0).left pt) (U := ⊤) (Set.mem_univ _)
  have h0 : ⊤ ≤ (e' 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker' : (ex.ker : Set (Fin g → ℂ)) = Λ := Set.ext fun z ↦ hker z
  have hholG : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z ↦ (e z).left ≫ α.left) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp he.2.2.1 α.left
  have hS0 : (0 : Additive (Over.mk y ⟶ G)) ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U} := by
    rw [← map_zero ex]
    exact h0
  have hsep : ∀ a ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U},
      ∀ b ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U},
      (∀ s : Γ(G.left, U), valAt' (Additive.toMul a).left U s = valAt' (Additive.toMul b).left U s) → a = b := by
    intro a ha b hb h
    exact Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
      (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦
        (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))))
  have hSe : IsOpen {z : Fin g → ℂ | ⊤ ≤ (e' z).left ⁻¹ᵁ U} := by
    have := (he'.2.2.1 U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hSG : IsOpen {z : Fin g → ℂ | ⊤ ≤ ((e z).left ≫ α.left) ⁻¹ᵁ U} := by
    have := (hholG U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hfe : ∀ s : Γ(G.left, U), DifferentiableOn ℂ (fun z ↦ valAt' (e' z).left U s) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ U} := by
    intro s
    have := (he'.2.2.1 U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hfG : ∀ s : Γ(G.left, U), DifferentiableOn ℂ (fun z ↦ valAt' ((e z).left ≫ α.left) U s)
      {z | ⊤ ≤ ((e z).left ≫ α.left) ⁻¹ᵁ U} := by
    intro s
    have := (hholG U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hD : ∀ w : Fin g → ℂ, (∀ s : Γ(G.left, U), fderiv ℂ (fun z ↦ valAt' (e' z).left U s) 0 w = 0) → w = 0 := by
    intro w hw
    obtain ⟨v, hv, -⟩ := he'.2.2.2.1 w
    obtain ⟨v0, hv0, -⟩ := he'.2.2.2.1 0
    have hvU : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff v.left U).2 (hv.1 ▸ h0)
    have hv0U : ⊤ ≤ v0.left ⁻¹ᵁ U := (top_le_preimage_iff v0.left U).2 (hv0.1 ▸ h0)
    have key : ∀ (u : Sp (DualNumber ℂ) ⟶ G.left) (hu : ⊤ ≤ u ⁻¹ᵁ U) (x : Sp ℂ ⟶ G.left) (hx : ⊤ ≤ x ⁻¹ᵁ U)
        (s : Γ(G.left, U)), spMap fstC ≫ u = x → (evalPt u U hu s).fst = evalPt x U hx s := by
      rintro u hu x hx s rfl
      exact (evalPt_spMap_comp fstC u U hu hx s).symm
    have heq : v.left = v0.left := by
      refine ext_evalPt (R := DualNumber ℂ) hU hvU hv0U (RingHom.ext fun s ↦ TrivSqZeroExt.ext ?_ ?_)
      · exact (key _ hvU _ h0 s hv.1).trans (key _ hv0U _ h0 s hv0.1).symm
      · have a := hv.2 U hvU s
        have b := hv0.2 U hv0U s
        rw [map_zero] at b
        exact a.trans ((hw s).trans b.symm)
    have hv0' : IsDerivAt0 (fun z ↦ (e' z).left) w v0.left := heq ▸ hv
    exact (he'.2.2.2.2 v0 hv0.1).unique hv0' hv0
  obtain ⟨F, hF, hu⟩ := GlobalTheory.existsUnique_linear_lift_of_separating (ex := ex) (G := G') he'.2.1
    (hker' ▸ isDiscrete_iff_discreteTopology.2 hdisc)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(G.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    hS0 hsep hSe hSG hfe hfG hD
  exact ⟨F, hF, fun M hM ↦ hu M hM⟩

end GlobalTheory.ExpLin
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Nonempty (Model s (GlobalTheory.AbLaw.cechLB s (LB.triv X) D)) := by
  first | exact @GlobalTheory.CechPoset.model_cechLB | exact GlobalTheory.CechPoset.model_cechLB | (intros; apply GlobalTheory.CechPoset.model_cechLB <;> assumption)
end
