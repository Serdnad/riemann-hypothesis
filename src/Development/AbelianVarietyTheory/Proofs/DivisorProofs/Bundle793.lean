module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle758
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle674
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.dbar_energy_glued_section_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n1 C la (glue C la u) ≤ ENNReal.ofReal K * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  first | exact @GlobalTheory.OTY.GlueEnergy.energy_glue_le | exact GlobalTheory.OTY.GlueEnergy.energy_glue_le | (intros; apply GlobalTheory.OTY.GlueEnergy.energy_glue_le <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.nonvanishingSet_etale_stein : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n), A.IsSec Λ τ → A.Pos Λ (fun _ => 0) → Etale A (nz A τ) z → ∃ X : EtaleStein n (nz A τ), X.z = (fun y : nz A τ => z y) ∧ X.e = fun y : nz A τ => -Real.log (A.nsq Λ τ y) := by
  first | exact @GlobalTheory.nzEtaleStein | exact GlobalTheory.nzEtaleStein | (intros; apply GlobalTheory.nzEtaleStein <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.exists_isStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom →
    ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S)
      (g : Over.mk s ⟶ U), _root_.GlobalTheory.EtC.IsStalk O s ∧ ∃ v, g.left v = u := by
  intro S U hU u
  let 𝒰 := U.left.affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers u
  let R : CommRingCat := 𝒰.X (𝒰.idx u)
  let f : Spec R ⟶ U.left := 𝒰.f (𝒰.idx u)
  haveI : IsOpenImmersion f := 𝒰.map_prop _
  haveI := hU
  let j : Spec R ⟶ S := f ≫ U.hom
  let y' : Spec R := y
  haveI := y'.isPrime
  obtain ⟨O, hO, hAO, hloc, hsh, hind, hcomap⟩ :=
    _root_.GlobalTheory.StrictHensPrime.exists_sh_indEt R y'.asIdeal
  let φ : Spec (CommRingCat.of O) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R O))
  refine ⟨O, hO, φ ≫ j, Over.homMk (φ ≫ f) (by simp [j]),
    ⟨hsh, R, inferInstance, hAO, j, inferInstance, hind, rfl⟩, IsLocalRing.closedPoint O, ?_⟩
  have hφ : φ (IsLocalRing.closedPoint O) = y' := by
    apply PrimeSpectrum.ext
    rw [← hcomap]
    rfl
  show (φ ≫ f) (IsLocalRing.closedPoint O) = u
  change f (φ (IsLocalRing.closedPoint O)) = u
  rw [hφ]
  exact hy

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_strictlyHenselian_indEtale_over_prime : ∀ (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime], ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧ (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p := by
  first | (exact @GlobalTheory.StrictHensPrime.exists_sh_indEt) | (exact GlobalTheory.StrictHensPrime.exists_sh_indEt) | (intros; apply GlobalTheory.StrictHensPrime.exists_sh_indEt  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixUnr

theorem base_eq {X Y Z Y' Z' : Scheme.{0}} (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) (y : Z') : b' (c' y) = b (c (h y)) := by
  have := congrArg (fun k => k.base y) e
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using this

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) : ChartPull ((M.pull b').pull c') ((M.pull b).pull c) h where
  idx J := J
  le J y hy := by
    have h1 := mem_pull.1 (mem_pull.1 hy)
    show h y ∈ ((M.pull b).pull c).U J
    refine mem_pull.2 (mem_pull.2 ?_)
    rw [← base_eq b c b' c' h e y]; exact h1
  g y J J' hj hj' := by
    have hj2 : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J PUnit.unit) := mem_pull.1 hj
    have hj2' : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J' PUnit.unit) := mem_pull.1 hj'
    have hk : ∀ K : PUnit → PUnit → M.ι, y ∈ ((M.pull b').pull c').U K → h y ∈ ((M.pull b).pull c).U K := fun K hK =>
      mem_pull.2 (mem_pull.2 (by rw [← base_eq b c b' c' h e y]; exact mem_pull.1 (mem_pull.1 hK)))
    have hk2 : (h ≫ c) y ∈ (M.pull b).U (J PUnit.unit) := by
      have := mem_pull.1 (hk J hj); simpa using this
    have hk2' : (h ≫ c) y ∈ (M.pull b).U (J' PUnit.unit) := by
      have := mem_pull.1 (hk J' hj'); simpa using this
    rw [gm_pull_g (M.pull b') c' (𝟙 Z') y J J' hj hj', gm_pull_g M b' (𝟙 Z' ≫ c') y _ _ hj2 hj2',
      gm_pull_g (M.pull b) c h y J J' (hk J hj) (hk J' hj'), gm_pull_g M b (h ≫ c) y _ _ hk2 hk2']
    have e' : (𝟙 Z' ≫ c') ≫ b' = (h ≫ c) ≫ b := by rw [Category.id_comp, e, Category.assoc]
    rw [e']

theorem lbIso_pull_square {XA XB YA YB ZA ZB : Scheme.{0}} (L : LB XA) (M : LB XB) (φA : YA ⟶ XA) (φB : YB ⟶ XB)
    (Φ : YA ⟶ YB) (ψA : ZA ⟶ XA) (ψB : ZB ⟶ XB) (v : ZA ⟶ ZB) (χA : ZA ⟶ YA) (χB : ZB ⟶ YB)
    (hA : χA ≫ φA = ψA) (hB : χB ≫ φB = ψB) (hv : v ≫ χB = χA ≫ Φ)
    (H : LBIso (L.pull φA) ((M.pull φB).pull Φ)) : LBIso (L.pull ψA) ((M.pull ψB).pull v) :=
  LBIso.chartPull (chartPullSame L (fun _ => ψA) (fun _ => φA) (fun _ => 1) χA fun _ => hA.symm)
    (chartPullPullPull M φB Φ ψB v χA (by rw [← hB, ← Category.assoc, hv, Category.assoc])) H

end GlobalTheory.EndLoc.HomFixUnr

namespace GlobalTheory.EndLoc


open GlobalTheory.EndLoc.HomFixUnr in
theorem formallyUnramified_homFixRep : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B →
    FormallyUnramified R.π := by
  intro S A B _ _ _ _ L M Rp hA _
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let BT : Over (Spec R) := (Over.pullback f).obj B
  let ψA : AT.left ⟶ A.left := pullback.fst A.hom f
  let ψB : BT.left ⟶ B.left := pullback.fst B.hom f
  have hAT : IsGrpPullback AT A f ψA := isGrpPullback_pullback A f
  have hBT : IsGrpPullback BT B f ψB := isGrpPullback_pullback B f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have tr : ∀ (g : Spec R ⟶ Rp.H), g ≫ Rp.π = f → ∀ (G : Over S) [GrpObj G] (GH : Over Rp.H) [GrpObj GH]
      (φ : GH.left ⟶ G.left), IsGrpPullback GH G Rp.π φ →
      ∃ e : (Over.pullback f).obj G ≅ (Over.pullback g).obj GH, IsMonHom e.hom ∧
        IsGrpPullback ((Over.pullback f).obj G) GH g (e.hom.left ≫ pullback.fst GH.hom g) ∧
        (e.hom.left ≫ pullback.fst GH.hom g) ≫ φ = pullback.fst G.hom f := by
    intro g hgf G _ GH _ φ hG
    have h' : IsGrpPullback ((Over.pullback g).obj GH) G f (pullback.fst GH.hom g ≫ φ) :=
      ((isGrpPullback_pullback GH g).comp hG).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso (isGrpPullback_pullback G f) h'
    haveI := he
    exact ⟨e, he, ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback GH g)).congr (Category.id_comp _) rfl,
      by rw [Category.assoc, heφ]⟩
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : AT ⟶ BT) (χA : AT.left ⟶ Rp.AH.left)
      (χB : BT.left ⟶ Rp.BH.left), IsMonHom v ∧ IsGrpPullback AT Rp.AH g χA ∧ IsGrpPullback BT Rp.BH g χB ∧
        χA ≫ Rp.φA = ψA ∧ χB ≫ Rp.φB = ψB ∧ v.left ≫ χB = χA ≫ Rp.Φ.left := by
    intro g hgf
    obtain ⟨eA, heA, hpA, hφA⟩ := tr g hgf A Rp.AH Rp.φA Rp.pbA
    obtain ⟨eB, heB, hpB, hφB⟩ := tr g hgf B Rp.BH Rp.φB Rp.pbB
    haveI := heA
    haveI := heB
    haveI := Rp.hom
    have hie : eB.inv.left ≫ eB.hom.left = 𝟙 _ := by rw [← Over.comp_left, eB.inv_hom_id, Over.id_left]
    refine ⟨eA.hom ≫ (Over.pullback g).map Rp.Φ ≫ eB.inv, _, _, inferInstance, hpA, hpB, hφA, hφB, ?_⟩
    have hm : ((Over.pullback g).map Rp.Φ).left ≫ pullback.fst Rp.BH.hom g =
        pullback.fst Rp.AH.hom g ≫ Rp.Φ.left := pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  obtain ⟨v₁, χA₁, χB₁, hv₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩ := build g₁ rfl
  obtain ⟨v₂, χA₂, χB₂, hv₂, hpA₂, hpB₂, hχA₂, hχB₂, hχ₂⟩ := build g₂ hg.symm
  let I : Ideal R := RingHom.ker q.hom
  have hI : IsNilpotent I := ⟨2, hsq⟩
  let j : Sp (R ⧸ I) ⟶ Sp R := spMap (Ideal.Quotient.mk I)
  have hj : j ≫ g₁ = j ≫ g₂ := by
    let ε : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hq
    have hε : Spec.map q = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
      rw [← Spec.map_comp]
      congr 1
    haveI : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
    rw [hε, Category.assoc, Category.assoc] at hi
    exact (cancel_epi _).1 hi
  have hχA : pullback.fst AT.hom j ≫ χA₁ = pullback.fst AT.hom j ≫ χA₂ := by
    apply Rp.pbA.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχA₁, hχA₂]
    · rw [Category.assoc, Category.assoc, hpA₁.1.w, hpA₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : v₁ = v₂ := by
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT BT hAbT v₁ v₂ ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₁.left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₂.left from pullback.lift_fst _ _ _]
      apply hBT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ v₁.left) ≫ ψB
            = pullback.fst AT.hom j ≫ v₁.left ≫ χB₁ ≫ Rp.φB := by rw [hχB₁, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χA₁ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχ₁]
          _ = pullback.fst AT.hom j ≫ χA₂ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχA]
          _ = pullback.fst AT.hom j ≫ v₂.left ≫ χB₂ ≫ Rp.φB := by rw [reassoc_of% hχ₂]
          _ = (pullback.fst AT.hom j ≫ v₂.left) ≫ ψB := by rw [hχB₂, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w v₁, Over.w v₂]
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  have hL : LBIso (L.pull ψA) ((M.pull ψB).pull v₁.left) :=
    lbIso_pull_square L M Rp.φA Rp.φB Rp.Φ.left ψA ψB v₁.left χA₁ χB₁ hχA₁ hχB₁ hχ₁ Rp.iso
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT BT ψA ψB v₁ hAT hBT hv₁ hL
  have e1 := hg' g₁ ⟨rfl, χA₁, χB₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩
  have e2 := hg' g₂ ⟨hg.symm, χA₂, χB₂, hpA₂, hpB₂, hχA₂, hχB₂, by rw [hv]; exact hχ₂⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.regularForms_isBundle_projectiveCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  first | (exact @GlobalTheory.PD.omB_isBundle) | (exact GlobalTheory.PD.omB_isBundle) | (intros; apply GlobalTheory.PD.omB_isBundle  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.complementaryModule_standardOpens_iff : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ z : K, (∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) ↔ ∃ y ∈ omB k K (rB k K x I) d, τ y = z := by
  first | (exact @GlobalTheory.ComplStd.complementary_iff) | (exact GlobalTheory.ComplStd.complementary_iff) | (intros; apply GlobalTheory.ComplStd.complementary_iff  <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.schwartzBruhat_fixed_near_one_siegelParabolic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  first | exact @GlobalTheory.KSp.parFun_fixed_near_one | exact GlobalTheory.KSp.parFun_fixed_near_one | (intros; apply GlobalTheory.KSp.parFun_fixed_near_one <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.weilRepresentation_intertwines_heisenberg : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  first | exact @GlobalTheory.KSp.weil_heis_intertwine | exact GlobalTheory.KSp.weil_heis_intertwine | (intros; apply GlobalTheory.KSp.weil_heis_intertwine <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.fourier_intertwines_siegelLeviOperator : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, weyl c ν * p = q * weyl c ν → ∀ φ : Matrix α ν E → ℂ, fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c q) (fou c ψ Q μ φ) := by
  first | exact @GlobalTheory.KSp.fou_parFun_levi | exact GlobalTheory.KSp.fou_parFun_levi | (intros; apply GlobalTheory.KSp.fou_parFun_levi <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.KSp.parFun_lintegral_sq | exact GlobalTheory.KSp.parFun_lintegral_sq | (intros; apply GlobalTheory.KSp.parFun_lintegral_sq <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' k'' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]
  [Field k''] [CharP k'' p]

theorem wittMap_injective (σ : k →+* k') :
    Function.Injective ((algebraMap (WittVector p k') (Fr p k')).comp (WittVector.map σ)) :=
  (IsFractionRing.injective (WittVector p k') (Fr p k')).comp (WittVector.map_injective σ σ.injective)

def frMap (σ : k →+* k') : Fr p k →+* Fr p k' := IsFractionRing.lift (wittMap_injective p σ)

theorem frMap_algebraMap (σ : k →+* k') (w : WittVector p k) :
    frMap p σ (algebraMap _ _ w) = algebraMap _ _ (WittVector.map σ w) :=
  IsFractionRing.lift_algebraMap _ _

theorem frMap_id : frMap p (RingHom.id k) = RingHom.id (Fr p k) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp [frMap_algebraMap, WittVector.map_id]

theorem frMap_comp (σ : k →+* k') (τ : k' →+* k'') :
    frMap p (τ.comp σ) = (frMap p τ).comp (frMap p σ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap]
  congr 1

theorem map_lift {ι : Type} (σ : k →+* k') (f : MvPowerSeries ι k) :
    MvPowerSeries.map (frMap p σ) (lift p f) = lift p (MvPowerSeries.map σ f) := by
  ext α
  rw [coeff_map, coeff_lift, coeff_lift, frMap_algebraMap, WittVector.map_teichmuller, coeff_map]

theorem map_subst_lift {d e : ℕ} (τ : k' →+* k'') (ψ : Fin d → MvPowerSeries (Fin e) k')
    (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : MvPowerSeries (Fin d) (Fr p k')) :
    MvPowerSeries.map (frMap p τ) (subst (fun j => lift p (ψ j)) g) =
      subst (fun j => lift p (MvPowerSeries.map τ (ψ j))) (MvPowerSeries.map (frMap p τ) g) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero fun j => constantCoeff_lift p (hψ j))]
  simp only [map_lift]

theorem lift_X_pow {ι : Type} (i : ι) (n : ℕ) :
    lift p ((X i : MvPowerSeries ι k) ^ n) = X i ^ n := by
  classical
  ext α
  rw [coeff_lift, coeff_X_pow, coeff_X_pow]
  split_ifs <;> simp

theorem frobRing_eq (h : (p : k) = 0) : frobRing h = frobenius k p :=
  RingHom.ext fun r => by rw [frobRing_apply, frobenius_def]

theorem frMap_frobenius [PerfectRing k p] : frMap p (frobenius k p) = KatzF.sig p k := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap, KatzF.sig, WittVector.FractionRing.frobenius]
  rw [RingEquiv.coe_toRingHom, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  rw [← WittVector.frobenius_eq_map_frobenius]
  rfl

theorem subst_lift_X_pow_frob [PerfectRing k p] (h : (p : k) = 0) {d : ℕ}
    (f : MvPowerSeries (Fin d) (Fr p k)) :
    subst (fun j => lift p ((X j : MvPowerSeries (Fin d) k) ^ p)) (MvPowerSeries.map (frMap p (frobRing h)) f) =
      KatzF.frobS p f := by
  simp only [lift_X_pow, frobRing_eq p h, frMap_frobenius, KatzF.frobS]
  rfl

theorem ringHom_eq_of_app {q : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
    {σ : O →+* O'} {τ : O' →+* O''} {υ : O →+* O''} {G : PDivGroup q O} {G' : PDivGroup q O'}
    {G'' : PDivGroup q O''} (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (h : ∀ n a, u.app n a = t.app n (s.app n a)) : υ = τ.comp σ := by
  ext r
  have e := h 0 (r • 1)
  rw [(u.app 0).smul_map, (s.app 0).smul_map, (t.app 0).smul_map, map_one, map_one, map_one] at e
  have := congrArg (Coalgebra.counit (R := O'')) e
  simpa [Algebra.smul_def] using this

end GlobalTheory.Katz
end
end
