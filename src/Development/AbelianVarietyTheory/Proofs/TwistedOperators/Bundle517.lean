module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolume
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle496
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle483
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle417
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle480
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt (ratClass classKernel)

theorem classKernel_eq_sum {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (g : H) (f : G → ℂ)
    (x : G) (T : Finset H) (hT : ∀ δ, f (x⁻¹ * ι δ * x) ≠ 0 → δ ∈ T) :
    classKernel ι.range (ι g) f x = ∑ δ ∈ T, {δ | IsConj g δ}.indicator (fun δ => f (x⁻¹ * ι δ * x)) δ := by
  let e : {δ | IsConj g δ} → ratClass ι.range (ι g) := fun δ => ⟨ι δ, by
    obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
    exact ⟨ι c⁻¹, ⟨_, rfl⟩, by rw [← hc]; simp⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (hι (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨⟨c⁻¹ * g * c, isConj_iff.2 ⟨c⁻¹, by simp⟩⟩, Subtype.ext (by simp [e])⟩
  rw [classKernel, ← (Equiv.ofBijective e he).tsum_eq fun δ => f (x⁻¹ * δ * x)]
  refine (tsum_subtype {δ | IsConj g δ} fun δ => f (x⁻¹ * ι δ * x)).trans (tsum_eq_sum fun δ hδ => ?_)
  by_contra h
  exact hδ (hT δ fun h0 => h (by simp [indicator, h0]))

theorem finsum_eq_sum_classKernel {G H I : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι)
    (p : H → Prop) (g : I → H) (hp : ∀ δ, p δ ↔ ∃ i, IsConj (g i) δ) (hg : ∀ i j, IsConj (g i) (g j) → i = j)
    (f : G → ℂ) (S : Finset I) (hS : ∀ i ∉ S, ∀ x, f (x⁻¹ * ι (g i) * x) = 0) (x : G)
    (hx : {δ | f (x⁻¹ * ι δ * x) ≠ 0}.Finite) :
    ∑ᶠ δ : {δ // p δ}, f (x⁻¹ * ι δ.1 * x) = ∑ i ∈ S, classKernel ι.range (ι (g i)) f x := by
  classical
  rw [Finset.sum_congr rfl fun i _ => classKernel_eq_sum ι hι (g i) f x hx.toFinset fun δ h => hx.mem_toFinset.2 h,
    Finset.sum_comm]
  refine (finsum_set_coe_eq_finsum_mem (f := fun δ => f (x⁻¹ * ι δ * x)) {δ | p δ}).trans ?_
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset (s := hx.toFinset) _ fun δ h => by
    simpa using fun h0 => h (by simp [indicator, h0])]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  by_cases h : p δ
  · obtain ⟨i, hi⟩ := (hp δ).1 h
    have hiS : i ∈ S := by
      by_contra hn
      obtain ⟨c, hc⟩ := isConj_iff.1 hi
      refine hx.mem_toFinset.1 hδ ?_
      rw [← hS i hn ((ι c)⁻¹ * x), ← hc]
      simp [mul_assoc]
    rw [indicator_of_mem (show δ ∈ {δ | p δ} from h), Finset.sum_eq_single_of_mem i hiS fun j _ hj =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => hj (hg j i (hc.trans hi.symm))) _,
      indicator_of_mem (show δ ∈ {δ | IsConj (g i) δ} from hi)]
  · rw [indicator_of_notMem (show δ ∉ {δ | p δ} from h), Finset.sum_eq_zero fun j _ =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => h ((hp δ).2 ⟨j, hc⟩)) _]

theorem classKernel_eq_zero {G : Type} [Group G] (Γ : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    classKernel Γ γ f = 0 := by
  funext x
  refine (tsum_congr ?_).trans tsum_zero
  rintro ⟨_, c, -, rfl⟩
  rw [← h (c * x)]
  simp [mul_assoc]

theorem finite_of_eventually_eq_one {V Y : Type} [Finite Y] {C : V → Type} [∀ v, One (C v)] [∀ v, Finite (C v)]
    {X : ∀ v, Set (C v)} {p : (∀ v, X v) × Y → Prop} (A : Set {q // p q})
    (h : ∀ᶠ v in cofinite, ∀ i ∈ A, (i.1.1 v).1 = 1) : A.Finite := by
  have : Finite {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} := eventually_cofinite.1 h
  refine Set.Finite.of_finite_image
    (f := fun i : {q // p q} => ((fun v : {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} => i.1.1 v), i.1.2)) (Set.toFinite _)
    fun i hi j hj e => Subtype.ext (Prod.ext (funext fun v => ?_) (congrArg Prod.snd e :))
  by_cases hv : ∀ i ∈ A, (i.1.1 v).1 = 1
  · exact Subtype.ext ((hv i hi).trans (hv j hj).symm)
  · exact congrFun (congrArg Prod.fst e) ⟨v, hv⟩

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
  {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}

theorem exists_isCompact_tensor (ha : ∀ w, HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    ∃ C, IsCompact C ∧ ∀ y, tensor σ J fa ff y ≠ 0 → y ∈ C := by
  refine ⟨_, (infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod
    ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi ha))
      hf.tensorFin_mem.2), fun y hy => ?_⟩
  rw [tensor_eq_infFin] at hy
  exact ⟨fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hy) w (Finset.mem_univ w)),
    subset_tsupport _ (right_ne_zero_of_mul hy)⟩

theorem ne_zero_of_tensor (hf : IsFinFamily σ J L ff) {y : GAd σ J} (hy : tensor σ J fa ff y ≠ 0) (v) :
    ff v (proj σ J v y) ≠ 0 := by
  rw [tensor_eq_infFin] at hy
  simpa only [projFinLoc_projFin] using (hf.tensorFin_ne_zero_iff _).1 (right_ne_zero_of_mul hy) v


omit [NumberField F] [NumberField E] in
theorem charpoly_eq_of_isConj {γ δ : GRat σ J} (h : IsConj γ δ) : δ.1.1.charpoly = γ.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have : (c * γ * c⁻¹).1.1 = c.1.1 * γ.1.1 * (c.1⁻¹).1 := rfl
  rw [this, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end Adelic

theorem integral_polKernel : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  classical
  intro E _ _ F _ σ hCM hun r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  obtain ⟨H1, H2, H3⟩ := GlobalTheory.T.rational_unitary_classes_iff_local_class_families E F σ hCM hun r P J hJ
  obtain ⟨Ff, Fa⟩ := GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places F E σ hCM r P
  have hae := GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hCM r P J hJ L
  have hcl := GlobalTheory.T.rationalClassTerm_eq_volume_mul_prod_orbitalIntegrals F E σ hCM r P J hJ L μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  let I := {p : (∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) × (∀ w : InfinitePlace F, XSet P w.Completion J) //
    ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  obtain ⟨hsupp, hsum⟩ := finsum_restrictedFamily_eq_prod_finsum (HeightOneSpectrum (𝓞 F)) (InfinitePlace F)
    (fun v => Cls P (Fv F v)) (fun v => XSet P (Fv F v) J) (fun w => XSet P w.Completion J) (fun v => Set.toFinite _)
    (fun v => orbCls (μf v) (dtf v) (ff v)) (fun w => orbCls (μa w) (dta w) (fa w)) (by
      filter_upwards [hae, hff.2, hμ.eventually_eq_one, IsRestrictedProd.eventually_eq_one hdt] with v h1 h2 h3 h4
      rw [h2]
      exact ⟨h1.1, h1.2.2.2 _ _ (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) h3 h4⟩)
  choose g g1 g2 g3 using fun i : I => H3 (fun v => (i.1.1 v).1) (fun w => (i.1.2 w).1) (fun v => (i.1.1 v).2)
    (fun w => (i.1.2 w).2) i.2
  have hp : ∀ δ : GRat σ J, δ.1.1.charpoly = P.1 ↔ ∃ i, IsConj (g i) δ := fun δ => by
    refine ⟨fun h => ?_, fun ⟨i, hi⟩ => (charpoly_eq_of_isConj hi).trans (g1 i)⟩
    obtain ⟨a1, a2, a3⟩ := H1 δ h
    choose qf qf1 qf2 using a1
    choose qa qa1 qa2 using a2
    let i : I := ⟨(fun v => ⟨qf v, (qf1 v).mem⟩, fun w => ⟨qa w, (qa1 w).mem⟩), a3.mono fun v hv => (qf2 v 1 hv).symm⟩
    refine ⟨i, IsConj.symm ((H2 δ (g i) h (g1 i)).2 ⟨fun v q hq => ?_, fun w q hq => ?_⟩)⟩
    · rw [qf2 v q hq]; exact g2 i v
    · rw [qa2 w q hq]; exact g3 i w
  have hg : ∀ i j, IsConj (g i) (g j) → i = j := fun i j h => by
    obtain ⟨b1, b2⟩ := (H2 _ _ (g1 i) (g1 j)).1 h
    obtain ⟨a1, a2, -⟩ := H1 _ (g1 j)
    have e1 : ∀ v, i.1.1 v = j.1.1 v := fun v => Subtype.ext ((a1 v).unique (b1 v _ (g2 i v)) (g2 j v))
    have e2 : ∀ w, i.1.2 w = j.1.2 w := fun w => Subtype.ext ((a2 w).unique (b2 w _ (g3 i w)) (g3 j w))
    exact Subtype.ext (Prod.ext (funext e1) (funext e2))
  have hfin : {i : I | ∃ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) ≠ 0}.Finite := by
    refine finite_of_eventually_eq_one _ ?_
    filter_upwards [hae, hff.2] with v h1 h2
    rintro i ⟨x, hx⟩
    have h3 := ne_zero_of_tensor hff hx v
    rw [h2, map_mul, map_mul, map_inv] at h3
    exact h1.2.1 _ _ (g2 i v) ⟨_, by_contra fun hn => h3 (indicator_of_notMem hn _)⟩
  have hS : ∀ i ∉ hfin.toFinset, ∀ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) = 0 := fun i hi x =>
    by_contra fun h => hi (hfin.mem_toFinset.2 ⟨x, h⟩)
  obtain ⟨C, hC, hC'⟩ := exists_isCompact_tensor (fun w => (hfa w).2) hff
  have hker0 : ∀ x, polKernel P J (tensor σ J fa ff) x = ∑ i ∈ hfin.toFinset,
      classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff) x := fun x => by
    rw [polKernel, ← range_ratEmb]
    exact finsum_eq_sum_classKernel (ratEmb σ J) (ratEmb_injective σ J) _ g hp hg _ _ hS x
      (((GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hCM r J C hC).2 x).subset fun δ h => hC' _ h)
  have hker : descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) = fun q => ∑ i ∈ hfin.toFinset,
      descend (ratPts σ J) (classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff)) q := by
    funext q
    simp only [descend, hker0]
  have hi := fun i : I => hcl (g i) (g1 i) i.1.1 i.1.2 (g2 i) (g3 i)
  rw [hker]
  refine ⟨integrable_finsetSum _ fun i _ => (hi i).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hi i).1, Finset.sum_congr rfl fun i _ => (hi i).2, mul_assoc]
  simp only [Phi]
  rw [← hsum, mul_finsum' _ _ hsupp]
  refine (finsum_eq_sum_of_support_subset _ fun i hn => ?_).symm
  by_contra h
  refine hn ((hi i).2.symm.trans ?_)
  rw [classKernel_eq_zero _ _ _ (hS i h)]
  simp only [descend, Pi.zero_apply, integral_zero]

end GlobalTheory.TrEll
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ExchPf

open GlobalTheory.PairLift GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

def withForm (V : HSp D) (h : V.V →ₗ⋆[D.host.E] V.V →ₗ[D.host.E] D.host.E) (e : h = V.hT) : HSp D :=
  { V with hT := h, herm := e ▸ V.herm, nondeg := e ▸ V.nondeg, baseLattice_isUnimodular := e ▸ V.baseLattice_isUnimodular }

theorem HR_withForm (V : HSp D) (h : V.V →ₗ⋆[D.host.E] V.V →ₗ[D.host.E] D.host.E) (e : h = V.hT) :
    HR (AF D.host.F) D.sp.cm.sig V.gram = HR (AF D.host.F) D.sp.cm.sig (withForm V h e).gram := by
  subst e; rfl

theorem datum_withForm {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    (h : B.V →ₗ⋆[D.host.E] B.V →ₗ[D.host.E] D.host.E) (e : h = B.hT)
    (ω : GA D A × GA D (withForm B h e) →* Module.End ℂ (WO A (withForm B h e) → ℂ))
    (hd : IsWeilDatumO ψ A (withForm B h e) χ χ' ω) :
    IsWeilDatumO ψ A B χ χ' (ω.comp ((MonoidHom.id (GA D A)).prodMap (MulEquiv.subgroupCongr (HR_withForm B h e)).toMonoidHom)) := by
  subst e
  exact hd

theorem datum_negneg {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    (ω : GA D A × GA D (negSp (negSp B)) →* Module.End ℂ (WO A (negSp (negSp B)) → ℂ))
    (hd : IsWeilDatumO ψ A (negSp (negSp B)) χ χ' ω) :
    IsWeilDatumO ψ A B χ χ' (ω.comp ((MonoidHom.id (GA D A)).prodMap ((negGA B).trans (negGA (negSp B))).toMonoidHom)) := by
  have key := datum_withForm (ψ := ψ) (A := A) (B := B) (χ := χ) (χ' := χ') (-(-B.hT)) (neg_neg _) ω hd
  have e : ((negGA B).trans (negGA (negSp B))).toMonoidHom =
      (MulEquiv.subgroupCongr (HR_withForm B (-(-B.hT)) (neg_neg _))).toMonoidHom := MonoidHom.ext fun _ => rfl
  rw [e]
  exact key

theorem exch_eq_cj (A B : HSp D) (f : WO A B → ℂ) : exch A B f = cj id (dag A B f) := by
  funext x; simp [GlobalTheory.CoreOnto.exch, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag]

theorem theta_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (f : WO A B → ℂ) :
    IsThetaFunO ψ A B f ↔ IsThetaFunO ψ (negSp B) A (exch A B f) := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  rw [exch_eq_cj, ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ B A).1 (dag A B f)).2]
  exact ⟨hAB.theta f, fun h => by simpa only [GlobalTheory.WeilConj.dag_dag hAB] using hBA.theta _ h⟩

theorem heis_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (x : WO (negSp B) A)
    (f : WO A B → ℂ) : heisO ψ (negSp B) A x (exch A B f) = exch A B (heisO ψ A B (adjO A B x) f) := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  rw [exch_eq_cj, exch_eq_cj, ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ B A).2 x (dag A B f)).2, hAB.Heisenberg₂]

theorem sympl_negB (A B : HSp D) (x x' : WO B A) : symplO (negSp B) A x x' = -symplO B A x x' := by
  have e : hO (negSp B) A x x' = -hO B A x x' := by
    unfold hO
    rw [negSp_gram, GlobalTheory.CjNeg.inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem sympl_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (x x' : WO (negSp B) A) :
    symplO (negSp B) A x x' = symplO A B (adjO A B x) (adjO A B x') := by
  rw [(GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B).sympl, sympl_negB]

theorem bij_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) :
    Function.Bijective (adjO A B) :=
  Function.bijective_iff_has_inverse.2 ⟨adjO B A, fun x => (GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A).invol x,
    fun y => (GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B).invol y⟩

theorem covol_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    (m : Measure (Mx D B.rank A.rank)) (X : Set (Mx D B.rank A.rank)) (hX : IsCovolOne (ratL B A) m X) :
    ∃ m' X', IsCovolOne (ratL A (negSp B)) m' X' ∧ ∀ f f' : WO A B → ℂ,
      ∫ w in X, f w * starRingEnd ℂ (f' w) ∂m = ∫ w in X', exch A B f w * starRingEnd ℂ (exch A B f' w) ∂m' := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  obtain ⟨hμ, h𝓕, h1⟩ := hX
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D A.rank B.rank
  haveI : BorelSpace (WO A B) := ⟨rfl⟩
  haveI : BorelSpace (WO B A) := ⟨rfl⟩
  let eA : WO A B ≃+ WO B A :=
    { toFun := adjO B A
      invFun := adjO A B
      left_inv := fun x => hAB.invol x
      right_inv := fun y => hBA.invol y
      map_add' := hBA.add }
  let eH : WO A B ≃ₜ WO B A := ⟨eA.toEquiv, hBA.cont, hAB.cont⟩
  let eM : WO A B ≃ᵐ WO B A := eH.toMeasurableEquiv
  have hHaar : (m.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map m eA hBA.cont hAB.cont
  have hmp : MeasurePreserving eM m (m.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (m.map eM) m := MeasurePreserving.symm eM hmp
  let eG : ratL B A → ratL A B := fun g => ⟨adjO B A g, (hBA.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO A B g, (hAB.rat g).2 g.2⟩, Subtype.ext (hBA.invol g)⟩⟩
    have e := congrArg (fun x : ratL A B => adjO A B (x : WO B A)) hg
    simp only [eG, hAB.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL A B) (eM.symm ⁻¹' X) (m.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO A B (adjO B A g + x) = (g : WO A B) + adjO A B x
    rw [hAB.add, hAB.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' X) = X := by
    ext a; simp
  refine ⟨m.map eM, eM.symm ⁻¹' X, ⟨hHaar, hF, ?_⟩, fun f f' => ?_⟩
  · rw [MeasurableEquiv.map_apply, hpre, h1]
  · symm
    rw [MeasurableEquiv.restrict_map, integral_map_equiv, hpre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f (adjO A B (adjO B A x)) * starRingEnd ℂ (f' (adjO A B (adjO B A x))) = _
    rw [hAB.invol]

theorem weil_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ)) (hω : IsWeilDatumO ψ (negSp B) A χS χT ω) :
    ∃ ω', IsWeilDatumO ψ A B χT⁻¹ χS⁻¹ ω' ∧ Exch ψ ω ω' := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  have h1 := GlobalTheory.ConjWeil.weil_conjSource D ψ (negSp B) A χS χT ω hω
  obtain ⟨ω₃, h3, R⟩ := GlobalTheory.WeilConj.exists_conj_weilDatum D ψ (negSp (negSp B)) A χS⁻¹ χT⁻¹ (conjSource ω) h1
  refine ⟨_, datum_negneg ω₃ h3, fun f _ g h => ?_⟩
  have hadj : ∀ y : WO A B, adjO (negSp (negSp B)) A y = adjO B A y := by
    intro y; simp only [adjO, negSp_gram, neg_neg]
  have hf : dag (negSp (negSp B)) A (cj id (exch A B f)) = f := by
    funext y
    simp only [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, GlobalTheory.CoreOnto.exch, Complex.conj_conj, hadj, hAB.invol]
  have R' := R ((negGA (negSp B)) (negGA B h)) g (cj id (exch A B f))
  rw [hf] at R'
  show _ = exch A B (ω₃ (g, (negGA (negSp B)) (negGA B h)) f)
  rw [R', GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  funext x
  simp only [GlobalTheory.CoreOnto.exch, dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Complex.conj_conj, hadj, hBA.invol]

theorem exchLaw : ∀ D : D7, ExchLaw D := by
  intro D ψ A B hψ
  exact ⟨theta_exch hψ A B, heis_exch hψ A B, sympl_exch hψ A B, bij_exch hψ A B,
    fun m X hX => covol_exch hψ A B m X hX, fun χS χT ω hω => weil_exch hψ A B χS χT ω hω⟩

end GlobalTheory.ExchPf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧ (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧ (∀ k ∈ s.J, ∀ g, PiLocalization₂.val u v (g * k) = PiLocalization₂.val u v g) ∧ GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v)) ∧ ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ), heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  first | exact @GlobalTheory.EvenOnto.ConjVal.values_conj_hecke | exact GlobalTheory.EvenOnto.ConjVal.values_conj_hecke | (intros; apply GlobalTheory.EvenOnto.ConjVal.values_conj_hecke <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenThetaChainStage_levelMeasure_peterssonCoefficient : ∀ D : D7, ForStage D fun c _ s => (MeasurableSet (intOff c s) ∧ MeasurableSet s.big ∧ s.big ⊆ intOff c s ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ s.J, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F s.big s.ν ∧ ∫ g in s.big, F g ∂s.ν = ∫ b, f b ∂mR) ∧ ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ s.J, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.EvenOnto.MeasPet.meas_petco | exact GlobalTheory.EvenOnto.MeasPet.meas_petco | (intros; apply GlobalTheory.EvenOnto.MeasPet.meas_petco <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspMultiplicitySpace_span_sphericalEigenParts_eq_top : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e} = ⊤ := by
  first | exact @GlobalTheory.EvenOntoDecomp.cc_span_partFull | exact GlobalTheory.EvenOntoDecomp.cc_span_partFull | (intros; apply GlobalTheory.EvenOntoDecomp.cc_span_partFull <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenThetaChain_finiteDimensional_and_peterssonProducts : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D ∧ MetEx D := by
  first | exact @GlobalTheory.EvenMetric.finDim_and_metEx | exact GlobalTheory.EvenMetric.finDim_and_metEx | (intros; apply GlobalTheory.EvenMetric.finDim_and_metEx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomGrid

theorem bottom : All fun {D} _ {L} _ {G} _ _ => IsSelfDualC (Yc D 0) (L.ΛY 0) ∧ IsSelfDualC (G.V (.core 0)) (G.Λ (.core 0)) ∧ G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) ∧ zv G.sp.dec0 ∈ G.Λ (.core 0) ∧ (∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈ G.levCong (.core 0) → k ∈ levRow L) ∧ (Yc D 0).rank = D.R.r ∧ (G.V (.core 0)).rank = D.R.r + 1 ∧ ∀ (A : Fr (Yc D 0)) τ, (Finset.univ.filter fun a => A.ε τ a = false).card ≤ D.R.m := by
  intro D _ T L μ0 hL sc G W M _
  have hY : (⟨Yc D 0, L.ΛY 0⟩ : LSp D).IsV (Node.rank D (.grid 0 0)) (Node.neg D.R.m (.grid 0 0)) :=
    node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hP := G.sp.P_is 0 (Nat.zero_le _)
  refine ⟨hY.sd, hP.sd, G.sp.lat0, ?_, ?_, ?_, ?_, ?_⟩
  · show zv G.sp.dec0 ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, Submodule.zero_mem _, fun _ => 1, fun p => ?_, ?_⟩
    · exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    · funext i
      simp [zv, Matrix.mulVec, dotProduct]
  · intro k hk hfin
    have h1 : Lev.finE (Yc D 0) k ∈ congLev D.sp.cm (Yc D 0).gram (L.ΛY 0) G.modul := by
      refine GlobalTheory.T.congruence_level_of_embedding G.sp.dec0 (L.ΛY 0) (fun _ => 1) G.modul k ?_
      have e : G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := G.sp.lat0
      have := hfin
      unfold GridData.levCong at this
      rw [e] at this
      exact this
    have h2 := GlobalTheory.T.unitaryLatticeCongruence_mem_conjugateIdeal_inf (Yc D 0) (L.ΛY 0) hY.sd _ _ h1
    exact Subgroup.mem_inf.2 ⟨hk, congLev_mono (GlobalTheory.T.modulus_inf_conj_le_span_typePrimes_product G) h2⟩
  · simpa [Node.rank, rankV] using hY.rank
  · simpa [Node.rank, rankP, nRk] using hP.rank
  · intro A τ
    rw [GlobalTheory.T.card_negativeSigns_diagonalFrame_eq_signature _ hY.sigOK A τ, hY.sig]
    simp only [Node.neg, Nat.sub_zero]
    exact Nat.div_le_self _ _
end GlobalTheory.BottomGrid
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.congruence_preimage_volume_finite : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ μ : Measure (GfC Y), μ.IsHaarMeasure → MeasurableSet {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} ∧ 0 < μ {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} ∧ μ {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} < ⊤ := by
  first | exact @GlobalTheory.UnitaryEmbeddingVolume.vol_pos_lt_top | exact GlobalTheory.UnitaryEmbeddingVolume.vol_pos_lt_top | (intros; apply GlobalTheory.UnitaryEmbeddingVolume.vol_pos_lt_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isOpen_congruence_embedding : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → IsOpen {g : GA D V | Lev.finE V g ∈ congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪} := by
  first | exact @GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen | exact GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen | (intros; apply GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen <;> assumption)
end
