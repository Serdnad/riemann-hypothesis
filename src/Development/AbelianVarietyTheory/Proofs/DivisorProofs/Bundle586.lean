module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle533
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqZeroOfAffine
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_lift_algHom_of_etale_punctured : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] (φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B)), ∃ ψ : A →ₐ[R] B, (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R B))).comp ψ = φ := by
  first | exact @GlobalTheory.LiftHom.liftHom_of_etale_punctured | exact GlobalTheory.LiftHom.liftHom_of_etale_punctured | (intros; apply GlobalTheory.LiftHom.liftHom_of_etale_punctured <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E), (∀ x, T x = u * x * a) → LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  first | exact @GlobalTheory.KSp.det_restrictScalars_twoSidedMul | exact GlobalTheory.KSp.det_restrictScalars_twoSidedMul | (intros; apply GlobalTheory.KSp.det_restrictScalars_twoSidedMul <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R := by
  first | exact @GlobalTheory.exists_smooth_subalgebra_of_finset | exact GlobalTheory.exists_smooth_subalgebra_of_finset | (intros; apply GlobalTheory.exists_smooth_subalgebra_of_finset <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem sncAt_of_stalkId_eq_span_prod : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  intro Y _ I y hreg n r T hR hI
  refine ⟨hreg, ?_⟩
  choose O hO t ht using fun i => TopCat.Presheaf.exists_germ_eq Y.presheaf (r i)
  have hSo : IsOpen (⋂ i, (O i : Set Y)) := isOpen_iInter_of_finite fun i => (O i).2
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVS⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 hO) hSo
  have hle : ∀ i, V ≤ O i := fun i z hz => Set.mem_iInter.1 (hVS hz) i
  let f : Fin n → Γ(Y, V) := fun i => Y.presheaf.map (homOfLE (hle i)).op (t i)
  have hgf : ∀ i, Y.presheaf.germ V y hyV (f i) = r i := fun i => by
    simp only [f]; rw [TopCat.Presheaf.germ_res_apply]; exact ht i
  let a : Γ(Y, V) := ∏ i ∈ T, f i
  have hga : Y.presheaf.germ V y hyV a = ∏ i ∈ T, r i := by
    simp only [a, map_prod, hgf]
  let V' : Y.affineOpens := ⟨V, hV⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian V'
  have hmap := WMult.stalkId_eq_map_germ I y V' hyV
  rw [hI] at hmap

  obtain ⟨h₂, hu₂, hm₂⟩ := IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV (I.ideal V') (t := a)
    (by show _ ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V')
        rw [← hmap, hga]; exact Ideal.mem_span_singleton_self _)

  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I.ideal V') : (I.ideal V').FG)
  have hgen : ∀ g : s, ∃ d : Γ(Y, V), IsUnit (Y.presheaf.germ V y hyV d) ∧ d * g.1 ∈ Ideal.span {a} := by
    intro g
    apply IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV
    have hg : g.1 ∈ I.ideal V' := hs ▸ Submodule.subset_span g.2
    have : Y.presheaf.germ V y hyV g.1 ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V') :=
      Ideal.mem_map_of_mem _ hg
    rw [← hmap, ← hga, ← Set.image_singleton, ← Ideal.map_span] at this
    exact this
  choose d hdu hdm using hgen
  let h₁ : Γ(Y, V) := ∏ g : s, d g
  have hu₁ : IsUnit (Y.presheaf.germ V y hyV h₁) := by
    simp only [h₁, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun g _ => hdu g
  have hcol : I.ideal V' ≤ Submodule.comap (LinearMap.mulLeft Γ(Y, V) h₁) (Ideal.span {a}) := by
    rw [← hs, Submodule.span_le]
    classical
    intro g hg
    show h₁ * g ∈ Ideal.span {a}
    have e : h₁ = (∏ g' ∈ Finset.univ.erase (⟨g, hg⟩ : s), d g') * d ⟨g, hg⟩ :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
    rw [e, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hdm ⟨g, hg⟩)
  let h : Γ(Y, V) := h₁ * h₂
  have hyD : y ∈ Y.basicOpen h := (Y.mem_basicOpen h y hyV).2 (by
    simp only [h, map_mul]; exact hu₁.mul hu₂)
  let D : Y.affineOpens := Y.affineBasicOpen (U := V') h
  let ρ := Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op
  have hρ : IsUnit (ρ h) := Y.toRingedSpace.isUnit_res_basicOpen h
  have hρ₁ : IsUnit (ρ h₁) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_left hρ
  have hρ₂ : IsUnit (ρ h₂) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_right hρ
  refine ⟨D, hyD, n, fun i => ρ (f i), T, ?_, ?_⟩
  · have e : (fun i => Y.presheaf.germ D.1 y hyD (ρ (f i))) = r := by
      funext i
      show Y.presheaf.germ (Y.basicOpen h) y hyD (ρ (f i)) = r i
      rw [TopCat.Presheaf.germ_res_apply]
      exact hgf i
    rw [e]; exact hR
  · rw [← I.map_ideal' (U := D) (V := V') (homOfLE (Y.basicOpen_le h)).op]
    show Ideal.map ρ.hom (I.ideal V') = Ideal.span {∏ i ∈ T, ρ (f i)}
    have ha : ∏ i ∈ T, ρ (f i) = ρ a := by simp only [a, map_prod]
    rw [ha]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : h₁ * x ∈ Ideal.span {a} := hcol hx
      have h2 : ρ (h₁ * x) ∈ Ideal.span {ρ a} := by
        rw [← Set.image_singleton, ← Ideal.map_span]; exact Ideal.mem_map_of_mem _ h1
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₁] at h2
      exact h2
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have h2 : ρ (h₂ * a) ∈ Ideal.map ρ.hom (I.ideal V') := Ideal.mem_map_of_mem _ hm₂
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₂] at h2
      exact h2
end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

variable {T T₁ : Scheme.{0}}

theorem isPb (Y : Over T) : IsPullback (fst Y Y).left (snd Y Y).left Y.hom Y.hom :=
  IsPullback.of_hasPullback Y.hom Y.hom

theorem tens_hom (Y : Over T) : (Y ⊗ Y).hom = (fst Y Y).left ≫ Y.hom := (Over.w (fst Y Y)).symm

noncomputable def incl (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : (Y₁ ⊗ Y₁).left ⟶ (Y ⊗ Y).left :=
  (isPb Y).lift ((fst Y₁ Y₁).left ≫ j) ((snd Y₁ Y₁).left ≫ j) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, (isPb Y₁).w])

@[reassoc (attr := simp)] theorem incl_fst (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (fst Y Y).left = (fst Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_fst _ _ _

@[reassoc (attr := simp)] theorem incl_snd (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (snd Y Y).left = (snd Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_snd _ _ _

theorem incl_pullback (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (h : IsPullback j Y₁.hom Y.hom v) :
    IsPullback (incl v Y Y₁ j h.w) (Y₁ ⊗ Y₁).hom (Y ⊗ Y).hom v := by
  have w : incl v Y Y₁ j h.w ≫ (Y ⊗ Y).hom = (Y₁ ⊗ Y₁).hom ≫ v := by
    rw [tens_hom, tens_hom, incl_fst_assoc, h.w, Category.assoc]
  have e1 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (fst Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← tens_hom, s.condition]
  have e2 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (snd Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← (isPb Y).w, ← tens_hom, s.condition]
  let lf : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, s.pt ⟶ (Y₁ ⊗ Y₁).left := fun s =>
    (isPb Y₁).lift (h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s)) (h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s))
      (by rw [h.lift_snd, h.lift_snd])
  have lf1 : ∀ s, lf s ≫ (fst Y₁ Y₁).left = h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s) :=
    fun s => (isPb Y₁).lift_fst _ _ _
  have lf2 : ∀ s, lf s ≫ (snd Y₁ Y₁).left = h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s) :=
    fun s => (isPb Y₁).lift_snd _ _ _
  refine ⟨⟨w⟩, ⟨Limits.PullbackCone.IsLimit.mk w lf ?_ ?_ ?_⟩⟩
  · intro s
    apply (isPb Y).hom_ext
    · rw [Category.assoc, incl_fst, reassoc_of% (lf1 s), h.lift_fst]
    · rw [Category.assoc, incl_snd, reassoc_of% (lf2 s), h.lift_fst]
  · intro s
    rw [tens_hom Y₁, reassoc_of% (lf1 s), h.lift_snd]
  · intro s m hm1 hm2
    rw [tens_hom Y₁] at hm2
    apply (isPb Y₁).hom_ext
    · rw [lf1]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_fst v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd]; simpa only [Category.assoc] using hm2
    · rw [lf2]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_snd v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd, ← hm2, Category.assoc, (isPb Y₁).w]

theorem incl_mul (f : T₁ ⟶ T) (A : Over T) [GrpObj A] (B : Over T₁) [GrpObj B] (φ : B.left ⟶ A.left)
    (h : IsGrpPullback B A f φ) : incl f A B φ h.1.w ≫ (μ[A]).left = (μ[B]).left ≫ φ := by
  let x₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((fst B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  let y₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((snd B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, ← (isPb B).w, Over.w])
  have hm := h.2 (B ⊗ B) (fst B B) (snd B B) x₀ y₀ rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at hm
  have e : incl f A B φ h.1.w = (lift x₀ y₀).left := by
    apply (isPb A).hom_ext
    · rw [incl_fst, ← Over.comp_left, lift_fst]; rfl
    · rw [incl_snd, ← Over.comp_left, lift_snd]; rfl
  rw [e]; exact hm

theorem colim_of_pullbacks {T T₁ T₂ : Scheme.{0}} (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T)
    (hT : Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) (Y : Over T) (Y₁ : Over T₁) (Y₂ : Over T₂)
    (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left)
    (h₁ : IsPullback j₁ Y₁.hom Y.hom v₁) (h₂ : IsPullback j₂ Y₂.hom Y.hom v₂) :
    Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w))) := by
  refine (((BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hT)
    (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w)) (Y₁ ⊗ Y₁).hom (Y₂ ⊗ Y₂).hom (Y ⊗ Y).hom
    ?_ ?_).2 ⟨incl_pullback v₁ Y Y₁ j₁ h₁, incl_pullback v₂ Y Y₂ j₂ h₂⟩)
  · exact (incl_pullback v₁ Y Y₁ j₁ h₁).w.symm
  · exact (incl_pullback v₂ Y Y₂ j₂ h₂).w.symm

end GlobalTheory.ProdGlue

open GlobalTheory.ProdGlue in
theorem GlobalTheory.ProdGlue.mul_glue : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂) (A₁ : Over S₁) [GrpObj A₁] (A₂ : Over S₂) [GrpObj A₂] (B₁ : Over T₁) [GrpObj B₁] (B₂ : Over T₂) [GrpObj B₂] (A₀ : Over T) [GrpObj A₀] (i₁ : B₁.left ⟶ A₁.left) (i₂ : B₂.left ⟶ A₂.left) (j₁ : B₁.left ⟶ A₀.left) (j₂ : B₂.left ⟶ A₀.left), IsGrpPullback B₁ A₁ f₁ i₁ → IsGrpPullback B₂ A₂ f₂ i₂ → IsGrpPullback B₁ A₀ v₁ j₁ → IsGrpPullback B₂ A₀ v₂ j₂ → ∀ (i : A₀.left ⟶ A₁.left ⨿ A₂.left), j₁ ≫ i = i₁ ≫ Limits.coprod.inl → j₂ ≫ i = i₂ ≫ Limits.coprod.inr → ∃ m : Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⟶ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)), ∀ l : (A₀ ⊗ A₀).left ⟶ (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))).left, l ≫ (fst (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (fst A₀ A₀).left ≫ i → l ≫ (snd (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (snd A₀ A₀).left ≫ i → l ≫ m.left = (μ[A₀]).left ≫ i := by

  intro S S₁ S₂ T T₁ T₂ u₁ u₂ ⟨hS⟩ v₁ v₂ ⟨hT⟩ f₁ f₂ A₁ _ A₂ _ B₁ _ B₂ _ A₀ _ i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ i ei₁ ei₂
  set X := Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) with hX
  have hV := (BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hS)
    (Limits.BinaryCofan.mk (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) Limits.coprod.inr) A₁.hom A₂.hom X.hom
    (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm
  have pX : _ := hV.1 ⟨Limits.coprodIsCoprod _ _⟩
  have pX₁ : IsPullback (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) A₁.hom X.hom u₁ := pX.1
  have pX₂ : IsPullback (Limits.coprod.inr : A₂.left ⟶ A₁.left ⨿ A₂.left) A₂.hom X.hom u₂ := pX.2
  obtain ⟨cX⟩ := colim_of_pullbacks u₁ u₂ hS X A₁ A₂ _ _ pX₁ pX₂
  obtain ⟨c0⟩ := colim_of_pullbacks v₁ v₂ hT A₀ B₁ B₂ _ _ hj₁.1 hj₂.1
  have D := Limits.BinaryCofan.IsColimit.desc' cX
    ((μ[A₁]).left ≫ Limits.coprod.inl) ((μ[A₂]).left ≫ Limits.coprod.inr)
  let ml : (X ⊗ X).left ⟶ X.left := D.1
  have hm₁ : incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml = (μ[A₁]).left ≫ Limits.coprod.inl := D.2.1
  have hm₂ : incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml = (μ[A₂]).left ≫ Limits.coprod.inr := D.2.2
  have hw : ml ≫ X.hom = (X ⊗ X).hom := by
    apply Limits.BinaryCofan.IsColimit.hom_ext cX
    · change incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml ≫ X.hom = incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₁, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inl_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
    · change incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml ≫ X.hom = incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₂, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inr_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
  refine ⟨Over.homMk ml hw, fun l hl₁ hl₂ => ?_⟩
  change l ≫ ml = _
  have key : ∀ {Tk Sk : Scheme.{0}} (vk : Tk ⟶ T) (uk : Sk ⟶ S) (fk : Tk ⟶ Sk) (Ak : Over Sk) [GrpObj Ak]
      (Bk : Over Tk) [GrpObj Bk] (ik : Bk.left ⟶ Ak.left) (jk : Bk.left ⟶ A₀.left) (ink : Ak.left ⟶ X.left)
      (hik : IsGrpPullback Bk Ak fk ik) (hjk : IsGrpPullback Bk A₀ vk jk) (eik : jk ≫ i = ik ≫ ink)
      (κ : (Ak ⊗ Ak).left ⟶ (X ⊗ X).left)
      (κf : κ ≫ (fst X X).left = (fst Ak Ak).left ≫ ink) (κs : κ ≫ (snd X X).left = (snd Ak Ak).left ≫ ink)
      (hmk : κ ≫ ml = (μ[Ak]).left ≫ ink),
      incl vk A₀ Bk jk hjk.1.w ≫ l ≫ ml = incl vk A₀ Bk jk hjk.1.w ≫ (μ[A₀]).left ≫ i := by
    intro Tk Sk vk uk fk Ak _ Bk _ ik jk ink hik hjk eik κ κf κs hmk
    have e : incl vk A₀ Bk jk hjk.1.w ≫ l = incl fk Ak Bk ik hik.1.w ≫ κ := by
      apply (isPb X).hom_ext
      · rw [Category.assoc, hl₁, incl_fst_assoc, eik, Category.assoc, κf, incl_fst_assoc]
      · rw [Category.assoc, hl₂, incl_snd_assoc, eik, Category.assoc, κs, incl_snd_assoc]
    rw [reassoc_of% e, hmk, reassoc_of% (incl_mul fk Ak Bk ik hik), reassoc_of% (incl_mul vk A₀ Bk jk hjk), eik]
  apply Limits.BinaryCofan.IsColimit.hom_ext c0
  · exact key v₁ u₁ f₁ A₁ B₁ i₁ j₁ _ hi₁ hj₁ ei₁ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₁
  · exact key v₂ u₂ f₂ A₂ B₂ i₂ j₂ _ hi₂ hj₂ ei₂ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₂
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

theorem inv_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

end GlobalTheory.SymSpread
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnifTangent

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem eq_of_values {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x x' : Sp ℂ ⟶ X} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : ∀ f, valAt' x U f = valAt' x' U f) : x = x' := by
  refine (AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x h).symm.trans
    (Eq.trans ?_ (AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x' h'))
  congr 2
  ext1
  refine RingHom.ext fun f => ?_
  have := e f
  rw [valAt', valAt', dite_eq_left h, dite_eq_left h'] at this
  exact this

theorem fderiv_eq_zero_of_origin {w : Fin g → ℂ}
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0)
    (z : Fin g → ℂ) (U : A.left.Opens) (f : Γ(A.left, U)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) :
    fderiv ℂ (fun z => valAt' (u.ex z).left U f) z w = 0 := by
  let τ : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A
  have hτ : ∀ v, u.ex v ≫ τ = u.ex (z + v) := fun v => by
    rw [u.ex_add, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (τ.left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, hτ, add_zero]
    exact h
  have e : (fun v => valAt' (u.ex v).left (τ.left ⁻¹ᵁ U) ((τ.left.app U).hom f)) =
      fun v => valAt' (u.ex (z + v)).left U f := funext fun v => by
    rw [valAt'_comp, ← Over.comp_left, hτ]
  have := hw _ ((τ.left.app U).hom f) h0
  rw [e, fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), add_zero] at this
  exact this

theorem eq_zero_of_fderiv_eq_zero (w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) : w = 0 := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := A.left)
    (x := (u.ex 0).left (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hx
  haveI := u.discrete
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set u.Λ))
  have hO0 : (0 : Fin g → ℂ) ∈ O := by
    have : (0 : u.Λ) ∈ Subtype.val ⁻¹' O := hOe ▸ rfl
    exact this
  have hc : Continuous fun t : ℂ => t • w := by fun_prop
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 ((((u.hol U 0).1).inter hO).preimage hc) 0
    (by simpa only [Set.mem_preimage, zero_smul] using ⟨h0, hO0⟩)
  have ht : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hd : ∀ f, ∀ t ∈ Metric.ball (0 : ℂ) ε, HasDerivAt (fun t : ℂ => valAt' (u.ex (t • w)).left U f) 0 t := by
    intro f t ht
    have h1 := ((u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds (hB ht).1)).hasFDerivAt
    have h2 := h1.comp_hasDerivAt t ((hasDerivAt_id t).smul_const w)
    rw [one_smul, fderiv_eq_zero_of_origin u hw _ U f (hB ht).1] at h2
    exact h2
  have he : u.ex (((ε / 2 : ℝ) : ℂ) • w) = u.ex ((0 : ℂ) • w) := by
    refine Over.OverMorphism.ext (eq_of_values hU (hB ht).1 (hB (Metric.mem_ball_self hε)).1 fun f => ?_)
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) ε).isPreconnected
      (fun t ht => (hd f t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hd f t ht).deriv) ht
      (Metric.mem_ball_self hε)
  rw [zero_smul, (u.ker 0).2 (zero_mem _), u.ker] at he
  have h3 : (⟨_, he⟩ : u.Λ) ∈ ({0} : Set u.Λ) := hOe ▸ (hB ht).2
  exact (smul_eq_zero.1 (congrArg Subtype.val h3)).resolve_left (Complex.ofReal_ne_zero.2 (by positivity))

theorem tangent_bijection (hs : SmoothOfRelativeDimension g A.hom) :
    (∀ v : epsR ℂ ⟶ A, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v : epsR ℂ ⟶ A, IsTangent v ∧ u.IsDiff w v :=
  TangentOrigin.tangent_bijection_of_values valAt'_rules A L g u
    (exists_coord_adapted (HolChart.exists_holomorphic_chart valAt'_rules existsUnique_point_of_ringHom
      exists_holomorphic_section_of_etale) A L g u hs (eq_zero_of_fderiv_eq_zero u))

end GlobalTheory.UnifTangent
end
end

section

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor


theorem _root_.GlobalTheory.T.exists_polarized_superlattice_of_riemann_form : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  first | exact @GlobalTheory.UnimodOver.exists_unimodular_overlattice | exact GlobalTheory.UnimodOver.exists_unimodular_overlattice | (intros; apply GlobalTheory.UnimodOver.exists_unimodular_overlattice <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsQProjOver f → IsLocallyNoetherian X := by
  first | exact @GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | exact GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | (intros; apply GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out


theorem _root_.GlobalTheory.T.proper_lift_trait_of_generic_lift : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by
  first | exact @GlobalTheory.proper_lift_trait | exact GlobalTheory.proper_lift_trait | (intros; apply GlobalTheory.proper_lift_trait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (T : Over S) (x : T ⟶ A) (c : ℕ), IsUnit (c : Γ(T.left, ⊤)) → x ^ c = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S) (g : Over.mk z ⟶ T), g ≫ x = 1) → x = 1 := by
  first | (exact @GlobalTheory.TorsionRigid.eq_one_of_geometric) | (exact GlobalTheory.TorsionRigid.eq_one_of_geometric) | (intros; apply GlobalTheory.TorsionRigid.eq_one_of_geometric  <;> assumption)
end
