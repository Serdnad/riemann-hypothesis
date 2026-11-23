module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle428
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle513
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinBasisSubsetOfIsField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle176
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc

section Generic

variable {G : Type} [Group G] {Q V V' W : Type} [Field Q] [AddCommGroup V] [Module Q V] [AddCommGroup V']
  [Module Q V'] [AddCommGroup W] [Module Q W] [FiniteDimensional Q V]

private theorem exists_inj_dual_tprod (ρ : Representation Q G V) (ρ' : Representation Q G V')
    (π : Representation Q G W) (b : W →ₗ[Q] V →ₗ[Q] V') (hb : ∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x))
    (hi : Function.Injective b) :
    ∃ f : W →ₗ[Q] Module.Dual Q V ⊗[Q] V', (∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) ∧
      Function.Injective f := by
  let e := dualTensorHomEquiv Q V V'
  refine ⟨e.symm.toLinearMap ∘ₗ b, fun g w => ?_, e.symm.injective.comp hi⟩
  have key : ∀ (t : Module.Dual Q V ⊗[Q] V') (x : V),
      e ((ρ.dual.tprod ρ') g t) (ρ g x) = ρ' g (e t x) := by
    intro t x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, hs, ht]
    | tmul f y => simp [e, Module.Dual.transpose_apply]
  apply e.injective
  ext x
  obtain ⟨x, rfl⟩ : ∃ y, ρ g y = x := ⟨ρ g⁻¹ x, by simp⟩
  rw [key]
  simp [hb]

end Generic

section Transport

variable {l : ℕ} [Fact l.Prime] {G H A V : Type} [Group G] [Group H] [CommRing A] [Algebra ℚ_[l] A]
  [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

private theorem admissible_transport_equiv (ψ : H →* GQ l) (e : G ≃* H) (ρ : Representation A G V) :
    (IsCr (ψ.comp e.toMonoidHom) ρ ↔ IsCr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) ∧
    (IsDr (ψ.comp e.toMonoidHom) ρ ↔ IsDr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
  have hr : (ψ.comp e.toMonoidHom).range = ψ.range := by
    ext x
    exact ⟨fun ⟨g, hg⟩ => ⟨e g, hg⟩, fun ⟨h, hh⟩ => ⟨e.symm h, by simpa using hh⟩⟩
  have h1 : Dcr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Dcr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Dcr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actC, resCoef]
  have h2 : Ddr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Ddr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Ddr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actD, resCoef]
  unfold IsCr IsDr
  rw [hr, h1, h2]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

section Field

variable {l : ℕ} [Fact l.Prime] (K : FinExt l) {V V' W : Type} [AddCommGroup V] [Module ℚ_[l] V]
  [AddCommGroup V'] [Module ℚ_[l] V'] [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] V]
  [FiniteDimensional ℚ_[l] V'] [FiniteDimensional ℚ_[l] W]
  (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V')
  (π : Representation ℚ_[l] ↥(GK K) W) (f : W →ₗ[ℚ_[l]] Module.Dual ℚ_[l] V ⊗[ℚ_[l]] V')
  (hf : ∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) (hi : Function.Injective f)
include hf hi

private theorem crys_hom (h : IsCrys ((PP l).PD K) ρ) (h' : IsCrys ((PP l).PD K) ρ') :
    IsCrys ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l _ _ T
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have h1 := GlobalTheory.RegularRing.fracInv hfit (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C) K
  have h2 := GlobalTheory.RegularRing.lineUnit hfit (GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)) K
  exact GlobalTheory.RegularRing.subCrys _ ℚ_[l] h1 _ _ _ π f hf hi
    (GlobalTheory.RegularRing.tensorCrys _ ℚ_[l] h1 h2 _ _ _ _
      (GlobalTheory.RegularRing.dualCrys _ ℚ_[l] h1 h2 _ ρ h) h')

private theorem dR_hom (h : IsDR ((PP l).PD K) ρ) (h' : IsDR ((PP l).PD K) ρ') :
    IsDR ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  have := K.2
  have hF := GlobalTheory.DRFil.isField_dR T
  have s : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ hF h
  have s' : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ' := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ' hF h'
  have sd : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ.dual :=
    GlobalTheory.DRFil.spans_dual_of_spans _ ρ ρ.dual (Module.Dual.eval ℚ_[l] V) hF
      (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id s
  have st : GlobalTheory.DRFil.Spans ((PP l).PD K) (ρ.dual.tprod ρ') :=
    GlobalTheory.DRFil.Spans.tensor _ (LinearEquiv.refl _ _) (fun g x y => by simp) sd s'
  have sw := GlobalTheory.DRSubQuot.spans_of_injective _ π _ f hf hF hi st
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.ddR_finite_le ((PP l).PD K) hF π
  exact le_antisymm h2 (GlobalTheory.DRFil.finrank_mul_le_finrank_DdR_of_spans _ π h1 sw)

end Field

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.isCrys_isDR_internalHom :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] {W : Type} [AddCommGroup W] [Module A W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] A W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul A W] (ρ : Representation A G V) (ρ' : Representation A G V') (π : Representation A G W), ContAction ρ → ContAction ρ' → ContAction π → ∀ b : W →ₗ[ℚ_[l]] V →ₗ[ℚ_[l]] V', (∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x)) → Function.Injective b → (IsCr φ ρ → IsCr φ ρ' → IsCr φ π) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ π) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ _ ρ ρ' π _ _ _ b hb hi
  obtain ⟨K, e, -, -, rfl, -⟩ := openField φ hφ
  obtain ⟨f, hf, hfi⟩ := exists_inj_dual_tprod
    (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A ↥(GK K) V))
    (resCoef ℚ_[l] (ρ'.comp e.symm.toMonoidHom : Representation A ↥(GK K) V'))
    (resCoef ℚ_[l] (π.comp e.symm.toMonoidHom : Representation A ↥(GK K) W)) b
    (fun g w x => hb (e.symm g) w x) hi
  rw [(admissible_transport_equiv _ e ρ).1, (admissible_transport_equiv _ e ρ').1, (admissible_transport_equiv _ e π).1, (admissible_transport_equiv _ e ρ).2,
    (admissible_transport_equiv _ e ρ').2, (admissible_transport_equiv _ e π).2, (isCrIff K _).1, (isCrIff K _).1, (isCrIff K _).1,
    (isCrIff K _).2, (isCrIff K _).2, (isCrIff K _).2]
  exact ⟨crys_hom K _ _ _ f hf hfi, dR_hom K _ _ _ f hf hfi⟩
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.AdmRes

variable {l : ℕ} [Fact l.Prime]

section Transport

variable {G G' A A' V : Type} [Group G] [Group G'] [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A']
  [AddCommGroup V] [Module A V] [Module A' V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [IsScalarTower ℚ_[l] A' V]
  {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A' G' V}

private theorem transport (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : (IsCr φ ρ ↔ IsCr φ' ρ') ∧ (IsDr φ ρ ↔ IsDr φ' ρ') := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  have hd : Ddr φ (resCoef ℚ_[l] ρ) = Ddr φ' (resCoef ℚ_[l] ρ') := by
    unfold Ddr
    rw [he.iInf_comp (fun g => LinearMap.ker (actD φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actD
    rw [hρ, h1]
  unfold IsCr IsDr
  rw [hr, hc, hd]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

private theorem field_case (K K' LL : FinExt l) (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) := by
  have := LL.2
  have : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 V
  obtain ⟨T⟩ := tiedP l
  have hres := GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K K' LL h V ρ
  rw [(isCrIff K ρ).1, (isCrIff K ρ).2, (isCrIff K' _).1, (isCrIff K' _).2, (isCrField K ρ).1, (isCrField K ρ).2.1,
    (isCrField K' _).1, (isCrField K' _).2.1]
  exact ⟨fun hc => (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (PP l) (AIP l) T K LL V ρ hc).1, hres.1, hres.2⟩

private theorem gal_case (K K' : FinExt l) (h : K.1 ≤ K'.1) {A V : Type} [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    (ρ : Representation A ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) := by
  let β : ↥(botExt l).1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI : Module ↥(botExt l).1 V := Module.compHom V (β : ↥(botExt l).1 →+* ℚ_[l])
  have hs : ∀ (c : ↥(botExt l).1) (x : V), c • x = β c • x := fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥(botExt l).1 V := ⟨fun a c x => by
    rw [hs, hs, Algebra.smul_def, map_mul, β.commutes, mul_smul]; rfl⟩
  haveI : ContinuousConstSMul ↥(botExt l).1 V := ⟨fun c => continuous_const_smul (β c)⟩
  let ρ' : Representation ↥(botExt l).1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add _
          map_smul' := fun c x => by
            rw [RingHom.id_apply, hs, hs]
            exact LinearMap.map_smul_of_tower _ _ _ }
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  have t1 := transport (φ := (GK K).subtype) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρ') id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  have t2 := transport (φ := (GK K').subtype) (ρ := (ρ.comp (incl h) : Representation A ↥(GK K') V))
    (φ' := (GK K').subtype) (ρ' := (ρ'.comp (incl h) : Representation ↥(botExt l).1 ↥(GK K') V)) id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  rw [t1.1, t1.2, t2.1, t2.2]
  exact field_case K K' (botExt l) h ρ'

end UpperTheory.V.Loc.AdmRes

open UpperTheory.V.Loc.AdmRes in
theorem UpperTheory.V.Loc.isCrys_isDR_restrict_openSubgroup :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → (IsCr φ ρ → IsDr φ ρ) ∧ ∀ H : Subgroup G, IsOpen (H : Set G) → (IsCr φ ρ → CrOn φ ρ H) ∧ (IsDr φ ρ ↔ IsDr (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _
  obtain ⟨K, e, -, -, he, hK, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  let ρK : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have t1 := transport (φ := φ) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρK) e e.surjective he'
    (fun g x => by simp [ρK])
  refine ⟨?_, fun H hH => ?_⟩
  · rw [t1.1, t1.2]
    exact (gal_case K K le_rfl ρK).1
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  obtain ⟨K', e', -, -, hf, hK', -, -⟩ := openField (φ.comp H.subtype) hφH
  have hf' : ∀ g, ((e' g : ↥(GK K')) : GQ l) = φ g := fun g => DFunLike.congr_fun hf g
  have hle : GK K' ≤ GK K := by
    rw [← hK, ← hK']
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h : K.1 ≤ K'.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup K'.1]
    exact IntermediateField.fixedField_le hle
  have t2 := transport (φ := φ.comp H.subtype) (ρ := (ρ.comp H.subtype : Representation A H V))
    (φ' := (GK K').subtype) (ρ' := (ρK.comp (incl h) : Representation A ↥(GK K') V)) e' e'.surjective hf'
    (fun g x => by
      have : incl h (e' g) = e g := Subtype.ext ((hf' g).trans (he' g).symm)
      simp [ρK, this])
  unfold CrOn
  rw [t1.1, t1.2, t2.1, t2.2]
  exact (gal_case K K' h ρK).2
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem exists_int_basis {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V), ∀ g i j, ‖e.repr (ρ g (e j)) i‖ ≤ 1 := by
  classical
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₀ := Module.finBasis ℚ_[l] V
  let Λ : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (e₀ p.2))
  have hc : Continuous fun g : G => (fun i j => e₀.repr (ρ g (e₀ j)) i) :=
    continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap (e₀.coord i)).comp (hρ _)
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨c, hc0, hcC⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    exact ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩
  have hle : Λ ≤ Submodule.span ℤ_[l] (Set.range fun i => c • e₀ i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, rfl⟩
    change ρ g (e₀ j) ∈ _
    rw [← e₀.sum_repr (ρ g (e₀ j))]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : ‖e₀.repr (ρ g (e₀ j)) i / c‖ ≤ 1 := by
      rw [norm_div]
      refine div_le_one_of_le₀ (le_trans ?_ hcC) (norm_nonneg _)
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm (fun i j => e₀.repr (ρ g (e₀ j)) i) i)).trans
        (hC _ ⟨g, rfl⟩)
    let z : ℤ_[l] := ⟨_, h1⟩
    have h2 : e₀.repr (ρ g (e₀ j)) i • e₀ i = z • c • e₀ i := by
      change _ = (e₀.repr (ρ g (e₀ j)) i / c) • c • e₀ i
      rw [smul_smul, div_mul_cancel₀ _ hc0]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Submodule.IsLattice ℚ_[l] Λ :=
    Submodule.IsLattice.of_fg ℚ_[l] ((Submodule.fg_span (Set.finite_range _)).of_le hle)
  haveI : Submodule.IsFullLattice ℚ_[l] Λ :=
    { span_eq_top := by
        rw [eq_top_iff, ← e₀.span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨(1, i), by simp⟩ }
  haveI : Module.Free ℤ_[l] Λ := Submodule.IsLattice.free ℚ_[l] Λ
  haveI : Module.Finite ℤ_[l] Λ := Submodule.IsLattice.finite ℚ_[l] Λ
  let b := Module.finBasis ℤ_[l] Λ
  have hst : ∀ g, ∀ x ∈ Λ, ρ g x ∈ Λ := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, j⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * h, j), by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Λ.add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Λ.smul_mem a hx
  refine ⟨_, b.extendOfIsFullLattice ℚ_[l], fun g i j => ?_⟩
  have h1 : ρ g (b.extendOfIsFullLattice ℚ_[l] j) =
      ∑ k, ((b.repr ⟨_, hst g _ (b j).2⟩ k : ℤ_[l]) : ℚ_[l]) • b.extendOfIsFullLattice ℚ_[l] k := by
    have := congrArg Λ.subtype (b.sum_repr ⟨_, hst g _ (b j).2⟩)

    rw [map_sum] at this
    convert this.symm using 1
    · rw [Basis.extendOfIsFullLattice_apply]; rfl
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Basis.extendOfIsFullLattice_apply]
      rfl
  rw [h1, Basis.repr_sum_self]
  exact PadicInt.norm_le_one _


open GlobalTheory.UnramifiedRep GlobalTheory.UnramifiedCrys GlobalTheory.Cyc in
private theorem isCrys_of_inertia {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    (K : FinExt l) (hχ : Continuous fun g => (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]))
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (hρ : ∀ x, Continuous fun g => ρ g x) (w : ℤ)
    (hI : ∀ g ∈ IK K, ∀ x, ρ g x = (((P.PD K).χ g ^ w : ℚ_[l]ˣ) : ℚ_[l]) • x) : IsCrys (P.PD K) ρ := by
  have := compactSpace_GK K
  let χ := (P.PD K).χ
  let ρ' : Representation ℚ_[l] ↥(GK K) V := twist (χ ^ (-w)) ρ
  have hρ' : ∀ g x, ρ' g x = ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • ρ g x := fun g x => rfl
  have hcont : ∀ x, Continuous fun g => ρ' g x := fun x => by
    simp only [hρ', Units.val_zpow_eq_zpow_val]
    exact (hχ.zpow₀ _ fun g => Or.inl (Units.ne_zero _)).smul (hρ x)
  have hI' : ∀ g ∈ IK K, ∀ x, ρ' g x = x := fun g hg x => by
    rw [hρ', hI g hg, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_smul]
  obtain ⟨n, e, hint⟩ := exists_int_basis ρ' hcont
  obtain ⟨M, hM⟩ := exists_matrixHom ρ' e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI' g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      rw [hM, hM, h, map_one, Module.End.one_apply])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (ρ' g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  obtain ⟨u, hu⟩ := (P.PD K).t_unit
  have hact : ∀ g, (P.PD K).actB g ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) =
      algebraMap ℚ_[l] P.R.B ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) * ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) := fun g => by
    have h1 : Units.map ((P.PD K).actB g : P.R.B →* P.R.B) u =
        Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (χ g) * u := by
      ext
      change (P.PD K).actB g u = algebraMap ℚ_[l] P.R.B (χ g : ℚ_[l]ˣ) * u
      rw [hu, (P.PD K).t_act, Algebra.smul_def]
    have h2 := congrArg (fun x : (P.R.B)ˣ => ((x ^ (-w) : (P.R.B)ˣ) : P.R.B)) h1
    beta_reduce at h2
    rw [mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul] at h2
    exact h2
  refine GlobalTheory.T.isCrys_of_split_alt (P.PD K) ρ e (((u ^ (-w) : (P.R.B)ˣ) : P.R.B) • AI.ιA.mapMatrix W) ?_ fun g => ?_
  · rw [Matrix.det_smul, ← RingHom.map_det]
    exact ((Units.isUnit _).pow _).mul (hW.map _)
  · conv_rhs => rw [← hB g]
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, map_mul, hact,
      hρ', map_smul, Finsupp.smul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem UpperTheory.V.Loc.crUnr :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Algebra ℤ_[l] A] [IsScalarTower ℤ_[l] ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → ∀ w : ℤ, (∀ g, φ g ∈ Iq l → ∀ x, ρ g x = ((cycA l l A (φ g) ^ w : Aˣ) : A) • x) → IsCr φ ρ := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ w hI
  obtain ⟨K, e, -, he, hφe, hr, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  obtain ⟨hc, -, hq⟩ := cycFacts l l
  have hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by
    rw [← hφe]
    simp
  let ρ' : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have hχ : ∀ g : ↥(GK K), ((((PP l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) :=
    fun g => by rw [(PP l).PD_χ, hq]
  have h1 : Crys K ρ' := by
    refine isCrys_of_inertia (PP l) (AIP l) T K ?_ _ (fun x => ?_) w fun g hg x => ?_
    · simp only [hχ]
      have h0 : Continuous fun g : ↥(GK K) => ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) :=
        Units.continuous_val.comp (hc.comp continuous_subtype_val)
      exact continuous_subtype_val.comp h0
    · exact hρ.comp (he.prodMk continuous_const)
    · change ρ (e.symm g) x = _
      rw [hI _ (by rw [hφ']; exact (memIK K g).1 hg), hφ']
      have h2 : cycA l l A g = Units.map (algebraMap ℚ_[l] A : ℚ_[l] →* A) (((PP l).PD K).χ g) := by
        ext
        change algebraMap ℤ_[l] A _ = algebraMap ℚ_[l] A _
        rw [hχ, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] A]
        rfl
      rw [h2, ← map_zpow]
      exact algebraMap_smul A _ x
  have h2 := (isCrIff K ρ').1.2 h1
  have h3 : Dcr φ (resCoef ℚ_[l] ρ) = Dcr (GK K).subtype (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    refine (e.symm.surjective.iInf_congr _ fun g => ?_).symm
    unfold actC
    rw [hφ']
    rfl
  unfold IsCr at h2 ⊢
  rw [h3, h2, hr, Subgroup.range_subtype]
end
