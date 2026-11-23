module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle136
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.PairingDivisors.StatementA
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleTrivializingTorsionAbelianSchem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Module

namespace GlobalTheory.GoodLat

section General

variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (N : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (N : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 N x hx; exact @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span)
  | exact @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span ..)

theorem isLattice_comap [IsNoetherianRing R] {U : Type} [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
    (N : Submodule R V) (hN : Submodule.IsLattice K N) (f : U →ₗ[K] V) (hf : Function.Injective f) :
    Submodule.IsLattice K (N.comap (f.restrictScalars R)) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (f.restrictScalars R) hf ?_
    exact hN.fg.of_le (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end General

section Forms

open Formalism.IndefR.Arith
open Formalism.DivisionValues.exponent_index_lattice (span_comap_eq_top)

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)


omit [Fintype G0] in
theorem isLattice_span_MK (hK : A.IsKsForm) (hM : A.MKFull) :
    Submodule.IsLattice LL (Submodule.span (𝓞 LL) (A.MK : Set WL)) := by
  obtain ⟨⟨s, hs⟩, hsp⟩ := hM
  refine ⟨⟨s, le_antisymm (Submodule.span_mono (hs ▸ Submodule.subset_span)) (Submodule.span_le.2 ?_)⟩, ?_⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih =>
      have e : a • x = (algebraMap (𝓞 Ks) (𝓞 LL) a) • x := by
        rw [← algebraMap_smul Ks a x, ← algebraMap_smul LL (algebraMap (𝓞 Ks) Ks a) x,
          ← algebraMap_smul LL (algebraMap (𝓞 Ks) (𝓞 LL) a) x]
        rfl
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ ih
  · obtain ⟨n, b, hb, -, -, -, h4⟩ := hK
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

private theorem span_MK_eq_top (hK : A.IsKsForm) (hM : A.MKFull) :
    Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL) = ⊤ := by
  obtain ⟨n, b, hb, -, -, -, hbt⟩ := hK
  apply top_unique
  rw [← hbt]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  have hx : b i ∈ Submodule.span Ks (A.MK : Set WL) := hM.2 ▸ hb i
  have hs : Submodule.span Ks (A.MK : Set WL) ≤
      (Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL)).restrictScalars Ks := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span (Submodule.subset_span hx)
  exact hs hx

theorem isFullLattice_Mcoord (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)
    {d : ℕ} (b : Fin d → WL) (hb : LinearIndependent LL b) (hW : ∀ i, b i ∈ A.Wgood J0 lam0 eC) :
    Submodule.IsFullLattice LL (A.Mcoord J0 lam0 eC b) := by
  let f := (Fintype.linearCombination LL b).restrictScalars (𝓞 LL)
  have e : A.Mcoord J0 lam0 eC b = (Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
      f := by
    ext c
    have hc : Fintype.linearCombination LL b c ∈ A.Wgood J0 lam0 eC := by
      rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hW i)
    exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hc.1⟩, hc.2⟩⟩
  rw [e]
  have hf : Function.Injective f := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun c hc => funext ?_)
    exact Fintype.linearIndependent_iff.1 hb c hc
  refine { toIsLattice := isLattice_comap _ (isLattice_span_MK A hK hM) (Fintype.linearCombination LL b) hf
           span_eq_top := span_comap_eq_top (Fintype.linearCombination LL b) _ (span_MK_eq_top A hK hM) }

theorem mj_full (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) :
    (A.Mj J0 lam0 eC).FG ∧ Submodule.span LL (A.Mj J0 lam0 eC : Set WL) = A.Wgood J0 lam0 eC := by
  have h := isLattice_comap _ (isLattice_span_MK A hK hM) (A.Wgood J0 lam0 eC).subtype Subtype.val_injective
  have e : A.Mj J0 lam0 eC = ((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
      ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))).map
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL)) := by
    ext x
    exact ⟨fun hx => ⟨⟨x, hx.1.2, hx.2⟩, hx.1.1, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact ⟨⟨hy, y.2.1⟩, y.2.2⟩⟩
  refine ⟨e ▸ h.fg.map _, ?_⟩
  rw [e]
  show Submodule.span LL ((A.Wgood J0 lam0 eC).subtype '' _) = _
  rw [Submodule.span_image]
  have hspan := span_MK_eq_top A hK hM
  have htop : Submodule.span LL
      (((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))) : Set (A.Wgood J0 lam0 eC)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_smul_mem (Submodule.span (𝓞 LL) (A.MK : Set WL))
      (show (x : WL) ∈ Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL) by rw [hspan]; trivial)
    have ha' : algebraMap (𝓞 LL) LL a ≠ 0 := by
      intro hz
      apply ha
      apply FaithfulSMul.algebraMap_injective (𝓞 LL) LL
      simpa using hz
    have hx : a • x ∈ ((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))) := hax
    have hx' := Submodule.smul_mem (Submodule.span LL
      (((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))) : Set (A.Wgood J0 lam0 eC)))
      (algebraMap (𝓞 LL) LL a)⁻¹ (Submodule.subset_span hx)
    rw [← algebraMap_smul LL a x, smul_smul, inv_mul_cancel₀ ha', one_smul] at hx'
    exact hx'
  rw [htop, Submodule.map_subtype_top]

end Forms

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mLat_of_full {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hK : ∀ i, (R.FW i).IsKsForm) (hM : ∀ i, (R.FW i).MKFull) (b : Bool) : (R.toCx F).MLat b := fun i =>
  isFullLattice_Mcoord (R.FW i) (hK i) (hM i) _ _ _ (R.bL F b i)
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))
    fun k => (Module.finBasis D.what₂.LL (R.WL F b i) k).2

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem mkFull_of_tie (t : FWTie T R κ v₀) (hl : LatFull T κ) (i : Fin D.R.m) : (R.FW i).MKFull := by
  refine mkFull_of _ ((R.FW i).WK.subtype ∘ₗ (t.e i).toLinearMap) ?_ (fun x => ?_) (hl i)
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_subtype_top]
  · constructor
    · intro hx
      obtain ⟨f, hf⟩ := (t.e i).surjective ⟨x, hx.1⟩
      have hfx : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = x := congrArg Subtype.val hf
      have h1 := (t.mem_MK i f).1 (hfx ▸ hx)
      exact ⟨f, fun la v hv => h1 la ⟨v, hv⟩, hfx⟩
    · rintro ⟨f, hf, rfl⟩
      exact (t.mem_MK i f).2 fun la y => hf la y.1 y.2

theorem mLat_of_tie (t : FWTie T R κ v₀) (hl : LatFull T κ) (F : Face D A) (b : Bool) : (R.toCx F).MLat b :=
  mLat_of_full R F t.ks (mkFull_of_tie t hl) b

end Record

end GlobalTheory.GoodLat
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorCompare

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

theorem eq_one_of_chrEq_one {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

variable {R i}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ D.R.r} {dict : GA D (Wc D i) → Σ k, Frame (U.X k).Ψ D.R.r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} {g : ℕ}
  {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
  {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {dδ : T0 → DeltaDat Xo c (Vc D i).rank}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) D.R.r}
  {dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r}
  {xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}

end Row

end GlobalTheory.TwistFactorCompare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct ComplexOrder MatrixOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteQuotient

theorem exists_bound_unitary {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  open scoped Matrix.Norms.L2Operator in
  obtain ⟨B, hB, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  obtain ⟨B, rfl⟩ := hB
  refine ⟨∑ i, ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖, fun g hg i j => ?_⟩
  have hu : B.1 * g * (B⁻¹).1 ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have : star (B.1 * g * (B⁻¹).1) * (B.1 * g * (B⁻¹).1) =
        star (B⁻¹).1 * (gᴴ * (star B.1 * B.1) * g) * (B⁻¹).1 := by
      simp only [star_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [this, hg, ← Matrix.mul_assoc, ← star_mul, Units.mul_inv, star_one, Matrix.one_mul, Units.mul_inv]
  have e : g = (B⁻¹).1 * (B.1 * g * (B⁻¹).1) * B.1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have h1 : ‖g i j‖ ≤ ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖ := by
    generalize B.1 * g * (B⁻¹).1 = u at hu e
    rw [e, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _)
      (entry_norm_bound_of_unitary hu k l)) (norm_nonneg _)
  refine h1.trans ?_
  refine (Finset.single_le_sum (f := fun j => ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖)
    (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖)
    (fun _ _ => by positivity) (Finset.mem_univ i)

theorem posDef_of_signature {n p : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G p 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq p 0 = 1 := by
    ext (i | i) (j | j)
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  have h2 : (star P.1 * G.reindex e e * P.1).PosDef := by
    have : star P.1 * G.reindex e e * P.1 = 1 := hP.trans h1
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

variable {D : D7}

theorem gram_hermND (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), GlobalTheory.StabCompact.det_gram_ne_zero V⟩

theorem cmExt (D : D7) : IsCMExt D.host.F D.host.E D.sp.cm.sig :=
  ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩

theorem isTotDef_of_posDef (V : HSp D) (h : ∀ τ, (gramAt D V τ).PosDef) : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := by
  refine ⟨D.sp.cm.totReal, fun ι => Or.inl fun x hx => ?_⟩
  have hτ := (cmExt D).2.2.2
  obtain ⟨τ, hι⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 (InfinitePlace.mk (Complex.ofRealHom.comp ι))
  have hι' : (tauE D τ).comp (algebraMap D.host.F D.host.E) = Complex.ofRealHom.comp ι := by
    rcases InfinitePlace.mk_eq_iff.1 hι with h1 | h1
    · exact h1
    · ext a
      have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h1 a)
      simpa using this
  have hpos : 0 < tauE D τ (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x) := by
    have hx' : (fun i => tauE D τ (x i)) ≠ 0 := fun e => hx (funext fun i => (tauE D τ).injective (by
      simpa using congrFun e i))
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 (h τ)).2 hx'
    convert this using 1

    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, mulVec, Finset.mul_sum, gramAt, Pi.star_apply,
    Matrix.map_apply, mul_assoc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hτ]; rfl
  obtain ⟨a, ha⟩ := (D.sp.cm.fixed (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x)).1 (by
    apply (tauE D τ).injective
    refine (hτ (tauE D τ) _).trans ?_
    exact Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 hpos).2.symm)
  refine ⟨a, ha, ?_⟩
  rw [← ha] at hpos
  have e : tauE D τ (algebraMap D.host.F D.host.E a) = (ι a : ℂ) := RingHom.congr_fun hι' a
  rw [e] at hpos
  exact_mod_cast hpos

theorem exists_compact : ∀ {D : D7} (V : HSp D), (∀ τ, (gramAt D V τ).PosDef) →
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  intro D V hV
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (cmExt D) (gram_hermND V) (isTotDef_of_posDef V hV)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_unitary (hV τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group


open MeasureTheory in
theorem integrableOn_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))),
    IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)),
    (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) →
    ∀ (μ : Measure (GA D S)) (𝓕 : Set (GA D S)), μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ →
    ∀ h, IntegrableOn (fun g => thetaKO om g h (L (F g))) 𝓕 μ := by
  intro D ψ _ S T χS χT om hom hS X _ _ _ L hL F hF hinv μ 𝓕 hμ h𝓕 h
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  obtain ⟨C, hC, hcov⟩ := exists_compact S hS
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D S) (GQ S) C hC (fun g => ?_) μ hμ 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · let b := Module.finBasis ℂ X
    have e : (fun g => thetaKO om g h (L (F g))) =
        fun g => ∑ k, b.coord k (F g) * om (g, h) (L (b k)) 0 := by
      funext g
      conv_lhs => rw [← b.sum_repr (F g)]

      simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact (b.coord k).continuous_of_finiteDimensional.comp hF
    · exact (hom.om_cont _ (hL (b k)) 0).comp (continuous_id.prodMk continuous_const)
  · intro γ hγ g
    have e : (γ * g, h) = ((γ, 1) : GA D S × GA D T) * (g, h) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [hinv γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hL _))

end GlobalTheory.DefiniteQuotient
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (Λ : ℂ → ℂ), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → IsHeckeL χ Λ → open Classical in IsToricSum φ s κ (condQ 𝔣 Q) χ (Λ s * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), Formalism.PairingDivisionLocalBalance.eq (Ideal.absNorm q.asIdeal) s (val χ (Pq q) : ℂ)) := by
  first | exact @GlobalTheory.ToricSumValue.toricSum_eq | exact GlobalTheory.ToricSumValue.toricSum_eq | (intros; apply GlobalTheory.ToricSumValue.toricSum_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_finite_etale_trivializing_torsion_abelianScheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (i : H ⟶ A₀), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ i ^ k = 1 ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → (∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 → g ^ k = 1) → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ φ₁ := by
  first | exact @UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme | exact UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme
end
