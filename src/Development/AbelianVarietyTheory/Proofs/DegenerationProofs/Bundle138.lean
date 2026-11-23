module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle080
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle129
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem eq_zero_of_cst_eq_zero {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} (p : X ⟶ Sp S) [Flat p] (x : X)
    (hx : p x = IsLocalRing.closedPoint S) {a : S} (ha : cst p x a = 0) : a = 0 := by
  let φ : S →+* X.presheaf.stalk x := (p.stalkMap x).hom.comp
    (((Sp S).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
  have hφ : ∀ c, φ c = cst p x c := fun c => by
    rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  have fl : φ.Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)) ?_) (Flat.stalkMap p x)
    have hU := isAffineOpen_top (Sp S)
    let _ := (Sp S).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
    have := hU.isLocalization_stalk ⟨p x, trivial⟩
    exact IsLocalization.flat ((Sp S).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp S).Opens)) : Sp S))
      (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl
  let _ := φ.toAlgebra
  have : Module.Flat S (X.presheaf.stalk x) := fl
  have : IsLocalHom (algebraMap S (X.presheaf.stalk x)) := ⟨fun c hc => by
    by_contra h
    exact cst_not_isUnit p x hx h (hφ c ▸ hc)⟩
  have : Module.FaithfullyFlat S (X.presheaf.stalk x) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective S (X.presheaf.stalk x) ((hφ a).trans (ha.trans (map_zero _).symm))

theorem coef_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  intro R _ _ _ I hI D A G _ _ U σ f th hE hth e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun χ hχ u b hb => ?_⟩
  have hI' : I ^ (e + 1) ≠ ⊤ := fun h => hI (top_unique (h ▸ Ideal.pow_le_self e.succ_ne_zero))
  haveI : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  haveI : IsLocalRing (R ⧸ I ^ (e + 1)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk (I ^ (e + 1))) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcl : thick R I e (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (I ^ (e + 1)))
  haveI := U.semi.smooth
  haveI : Flat (thickObj R I e G).hom := inferInstanceAs (Flat (pullback.snd G.hom (thick R I e)))
  obtain ⟨z₀, hz₀, hnz⟩ := hth (IsLocalRing.closedPoint R)
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let y : T ⟶ D.P.A := (U.gt e).pG
  let m : 𝟙_ _ ⊗ D.P.A ⟶ D.P.A := snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹
  let τ : D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (toUnit _) (𝟙 _ * cT D _ χ)
  have hc : ∀ {T₁ T₂ : Over (Spec (CommRingCat.of R))} (g : T₁ ⟶ T₂), g ≫ cT D _ χ = cT D _ χ := fun g => by
    rw [cT, ← Category.assoc, toUnit_unique (g ≫ toUnit _) (toUnit _)]
  have hmτ : m ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, inv_mul_cancel_right, Category.id_comp]
  have hyτ : y ≫ τ = lift (toUnit T) (y * cT D T χ) := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, lift_snd]
  have h1 : D.P.A.hom (m.left z₀) = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, Over.w m]; exact hz₀
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.P.A.hom) (g := thick R I e)
    (m.left z₀) (IsLocalRing.closedPoint (R ⧸ I ^ (e + 1))) (h1.trans hcl.symm)
  obtain ⟨z, rfl⟩ := (U.gt e).q_surj.1 w
  have hy : y.left z = m.left z₀ := hw
  have hz : (thickObj R I e G).hom z = IsLocalRing.closedPoint _ := by
    rw [← Over.w (U.gt e).q, Scheme.Hom.comp_apply]; exact hw'
  have h2 : (lift (toUnit T) (y * cT D T χ)).left z = z₀ := by
    rw [← hyτ, Over.comp_left, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, ← Over.comp_left, hmτ]
    rfl
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  have hu := (MulPullSec.mem_nonzeroLocus_iff th (lift (toUnit T) (y * cT D T χ)).left z hJ).1 (h2 ▸ hnz)
  have h0 := (hs T.left (𝟙 _) (lift (toUnit T) (fstG I e G)).left (lift (toUnit T) y).left
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z JG J hJG hJ).1 χ hχ
  have h3 := hb T y z J hJ
  rw [h0] at h3
  have h4 : cst T.hom z b = 0 := ((Units.isUnit _).mul hu).mul_left_eq_zero.1 h3.symm
  have h5 : cst (thickObj R I e G).hom z (Ideal.Quotient.mk _ b) = 0 :=
    (cst_comp (thickObj R I e G).hom (Ideal.Quotient.mk (I ^ (e + 1))) z b).symm.trans h4
  exact Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_cst_eq_zero _ z hz h5)

end GlobalTheory.PsiRing
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRatio

theorem exists_cstHom {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    ∃ φ : F →+* Z.presheaf.stalk z, (∀ c, cst p z c = φ c) ∧ ∀ c, gs (𝟙 _) z ⊤ (scal p c) = φ c := by
  refine ⟨(Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom), fun c => gs_eq p z ⊤ trivial _, fun c => ?_⟩
  exact gs_eq (𝟙 _) z ⊤ trivial _

theorem cst_eq_scal {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    cst p z c = gs (𝟙 _) z ⊤ (scal p c) := by
  obtain ⟨φ, h₁, h₂⟩ := exists_cstHom p z
  rw [h₁, h₂]

end GlobalTheory.PsiRatio

namespace GlobalTheory

theorem psiScal_eq_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by
  intro R _ _ D ga a f th hS hR hN χ q p hq hp
  let B : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let T : Over (Spec (CommRingCat.of R)) := TK R ⊗ B
  let pt : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨z₀, hz₀, hth⟩ := hN (jK R pt)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := jK R) (g := B.hom) pt z₀ hz₀.symm
  let z' : T.left := z
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z'
  let x : T ⟶ D.P.A := snd (TK R) B ≫ snd _ _
  have ex : lift (toUnit T) x = snd (TK R) B := by
    ext1
    · exact toUnit_unique _ _
    · exact lift_snd _ _
  have ey : x * (cT D T χ)⁻¹ * cT D T χ = x := inv_mul_cancel_right _ _
  have hu : IsUnit (sval th (snd (TK R) B).left z' J) := by
    refine (MulPullSec.mem_nonzeroLocus_iff th (snd (TK R) B).left z' hJ).1 ?_
    have : (snd (TK R) B).left z' = z₀ := hz
    rw [this]
    exact hth
  have e₁ := hR χ T (toUnit _) (fst (TK R) B) (x * (cT D T χ)⁻¹) z' J hJ
  have e₂ := (hS χ).2 T (fst (TK R) B) z' J hJ
  have e₃ := hq _ (snd (TK R) B).left z' J hJ
  have e₄ := hp T (x * (cT D T χ)⁻¹) z' J hJ
  rw [ey, ex] at e₁ e₄
  have e' : T.hom = (fst (TK R) B).left ≫ jK R := (Over.w (fst (TK R) B)).symm
  have e'' : (snd (TK R) B).left ≫ B.hom = (fst (TK R) B).left ≫ jK R := (Over.w (snd (TK R) B)).trans e'
  obtain ⟨φ, -, hφ⟩ := PsiRatio.exists_cstHom (F := FractionRing R) (fst (TK R) B).left z'
  have hc : ∀ c : R, cst ((fst (TK R) B).left ≫ jK R) z' c = φ (algebraMap R (FractionRing R) c) := fun c =>
    (PsiRatio.cst_eq_scal _ _ _).trans ((congrArg (gs (𝟙 _) z' ⊤) (PsiInt.scal_jK _ c)).trans (hφ _))
  have c₃ := (congrArg (fun s => cst s z' q) e'').trans (hc q)
  have c₄ := (congrArg (fun s => cst s z' p) e').trans (hc p)
  have alg : ∀ (A : Type) [CommRing A] (s s₀ t cq cp ca cq' cp' ca' : A) (u g r : Aˣ), IsUnit t →
      s = (u * r).val * s₀ → u.val = ca * g.val → s₀ = cq * t → s = cp * ((g * r).val * t) →
      cq = cq' → cp = cp' → ca = ca' → cq' * ca' = cp' := by
    intro A _ s s₀ t cq cp ca cq' cp' ca' u g r ht h₁ h₂ h₃ h₄ h₅ h₆ h₇
    subst h₅ h₆ h₇
    refine (((g * r).isUnit.mul ht).mul_left_inj).1 ?_
    rw [← h₄, h₁, h₃, Units.val_mul, Units.val_mul, h₂]
    ring
  apply φ.injective
  rw [map_mul]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ hu e₁ e₂ e₃ e₄ c₃ c₄ (hφ _)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiRing

theorem exists_isPullDeg_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hr gam hgam hψ hB
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨W, hW, ⟨ψW⟩⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW W).left, gW ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem y W ⟨_, hW⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ W) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine ⟨⟨e, me, v, hv, hE, ?_, xe, hc, W, ψW, gam ≫ gW,
    (Category.assoc _ _ _).trans ((congrArg (gam ≫ ·) hgW).trans hgam), fun x => ?_⟩, rfl, HEq.rfl, rfl⟩
  · exact (maps_iff v _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 hr
  · obtain ⟨b, -, vb⟩ := exists_up ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (D'.psi x) (D'.psi_gen x)
    have hx : D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = gam ≫ D.xK (xe x) :=
      (Category.assoc _ _ _).trans ((congrArg (jK V ≫ ·) (hc x)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D.c (xe x)).left) hgam.symm).trans (Category.assoc _ _ _))))
    refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · have e₁ := vb _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
      rw [pw, Fintype.prod_unique] at e₁
      refine (gm_res _ y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _)))))
      exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ y _ hy _))
    · obtain ⟨q, hq⟩ := exists_chart D'.P.isLB (D'.xK x y)
      obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
      have mp : (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.xK x y) ∈ D.P.L.U p := hp ▸ hJ _
      have e₁ := vb _ (𝟙 _) y (fun _ => p) (fun _ => q) (Set.mem_iInter.2 fun _ => mp) (Set.mem_iInter.2 fun _ => hq)
      have e₂ := hψ x _ (𝟙 _) y (fun _ => p) (fun _ => q) (fun _ => mp) (fun _ => hq)
      have w₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) (gam ≫ lam)).trans (val_pull hJ _ _ _))
      rw [Category.assoc, Category.assoc, l₁, l₂, Category.comp_id] at w₁
      refine (val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp])).trans (e₁.trans (e₂.symm.trans
        (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
      rw [Category.id_comp, Category.id_comp]
      exact (val_of (D.psi (xe x)) gam y J (fun _ => p) (fun _ => by rw [hp, hx])).symm.trans w₁.symm

end GlobalTheory.PsiRing

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem scalar_mem_of_psiIn : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → ∀ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), PsiScal D ga a → ∀ (x : D'.X) (J' : Ideal V), D'.PsiIn x J' → ∀ p q : R, algebraMap R (FractionRing R) q * (a (xe x)).val = algebraMap R (FractionRing R) p → ∃ m ∈ J', φ p = φ q * m := by
  intro R V _ _ _ _ _ φ D D' β v xe _ hv hc gam hgam hψ ga a hS x J' hJ' p q hpq
  obtain ⟨ga', a', hS'⟩ := exists_psiScal V D'
  obtain ⟨m₀, hm₀, em₀⟩ := (PsiScalIn.main_local D' ga' a' hS' x J').1 hJ'
  obtain ⟨t, ht, Ht⟩ := CubTransport.exists_pmaps ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => (D'.c x).left) (φ := fun _ => (D.c (xe x)).left) (ε := fun _ => -1) (spMap φ) (fun _ => hc x)
    (ga (xe x)) (hS (xe x)).1
  obtain ⟨c, hcu⟩ := exists_unit_val_eq_mul D'.P.isLB (hS' x).1 ht
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose I hI using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  choose I' hI' using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have gI : Good D.P.L (Z := (TK V).left) z I := hI
  have gI' : Good D'.P.L (Z := (TK V).left) z I' := hI'
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    change (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc x, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (D.c (xe x)).left) hgam.symm
  have e₁ := CubTransport.val_pmaps (fun _ => hx) (hψ x) (𝟙 _) gI gI'
  have e₂ := CubTransport.val_pmaps (fun _ => hc x) Ht (jK V) gI gI'
  have e₃ := (hS (xe x)).2 (Over.mk (gam ≫ jK R)) (Over.homMk gam rfl) z I gI
  have e₄ := (hS' x).2 (TK V) (𝟙 _) z I' gI'
  have e₅ := hcu _ (jK V) z I' gI'
  rw [Category.id_comp, Fintype.prod_unique, Category.id_comp] at e₁
  rw [Fintype.prod_unique, ← hgam] at e₂
  obtain ⟨Ω, f₁, f₂⟩ : ∃ Ω : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk z)ˣ,
      val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I' ∧
        val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) t (jK V) z I' := ⟨_, e₁, e₂⟩
  have f₃ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I).val =
      gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I).val := e₃
  have f₄ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I').val =
      PsiScalIn.sig z (a' x).val * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga' x) (jK V) z I').val :=
    e₄.trans (congrArg₂ (· * ·) (PsiScalIn.gs_scal_id z _) rfl)
  let u : V := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom c.val
  have hu : gs (jK V) z ⊤ c.val = PsiScalIn.sig z (algebraMap V _ u) := by
    refine Eq.trans (congrArg (gs (jK V) z ⊤) ?_) (PsiScalIn.gs_toOpen z ⊤ trivial u)
    simp [u, DegPre.toOpen]
  have key : gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) = PsiScalIn.sig z (algebraMap V _ (m₀ * u)) := by
    rw [f₁, f₂, Units.val_mul, Units.val_mul, f₄, mul_left_comm (gs _ _ _ _), Units.mul_right_inj] at f₃
    have f₅ := f₃.symm.trans (congrArg (PsiScalIn.sig z (a' x).val * ·) (e₅.trans (congrArg (· * _) hu)))
    rw [← _root_.mul_assoc, Units.mul_left_inj] at f₅
    rw [map_mul, map_mul, em₀]
    exact f₅
  have hs : ∀ r : R, gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (algebraMap R (FractionRing R) r)) =
      PsiScalIn.sig z (algebraMap V _ (φ r)) := fun r => by
    have k : ∀ {A : Type} [CommRing A] (w : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of A)) (s : A),
        gs (𝟙 _) z ⊤ (scal w s) = cst w z s := fun w s =>
      (gs_pull (𝟙 _) w z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
    refine (congrArg _ (PsiInt.scal_jK gam r).symm).trans ((k _ r).trans ?_)
    refine (congrArg (fun w => cst w z r) hgam).trans ((cst_comp (jK V) φ z r).trans ?_)
    refine Eq.trans ?_ (PsiScalIn.gs_toOpen z ⊤ trivial (φ r))
    exact (gs_res (jK V) z (U := ⊤) (V := ⊤) le_top trivial _).symm
  refine ⟨m₀ * u, J'.mul_mem_right u hm₀, IsFractionRing.injective V (FractionRing V) ((PsiScalIn.sig z).injective ?_)⟩
  rw [map_mul (algebraMap V _) (φ q), map_mul (PsiScalIn.sig z), ← hs, ← hs, ← key, ← hpq, ← gs_mul _ z ⊤ trivial]
  unfold scal
  rw [map_mul, map_mul]

end GlobalTheory.PsiRing
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_powerSeries :
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing O') C) (gam : K →+* C) (u : Cˣ), (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) ∧ (∀ r, ‖gam (algebraMap (PowerSeries O') K r)‖ ≤ 1) ∧ (u : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) ∧ ‖(u : C)‖ < 1 := by
  intro O' _ _ K _ _ _ _
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, hle, hlt⟩ :=
    exists_complete_isAlgClosed_cExt (PowerSeries (FractionRing O'))
      (FractionRing (PowerSeries (FractionRing O')))
  let ψ : PowerSeries (FractionRing O') →+* C :=
    (algebraMap (FractionRing (PowerSeries (FractionRing O'))) C).comp
      (algebraMap (PowerSeries (FractionRing O')) _)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing (PowerSeries (FractionRing O'))) C).injective.comp
      (IsFractionRing.injective (PowerSeries (FractionRing O')) (FractionRing (PowerSeries (FractionRing O'))))
  let φ : PowerSeries O' →+* C := ψ.comp (PowerSeries.map (algebraMap O' (FractionRing O')))
  have hφ : Function.Injective φ :=
    hψ.comp (PowerSeries.map_injective _ (IsFractionRing.injective O' (FractionRing O')))
  let _ : Algebra (PowerSeries O') C := φ.toAlgebra
  have : FaithfulSMul (PowerSeries O') C := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  let g : K →ₐ[PowerSeries O'] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : ∀ r, g.toRingHom (algebraMap (PowerSeries O') K r) = φ r := fun r => g.commutes r
  have hX : φ PowerSeries.X ≠ 0 := fun h =>
    PowerSeries.X_ne_zero (hφ (h.trans (map_zero φ).symm))
  refine ⟨C, i1, i2, i3, i4, (ψ.comp PowerSeries.C).toAlgebra, g.toRingHom, Units.mk0 _ hX,
    fun x => ?_, fun r => ?_, (hg _).symm, ?_⟩
  · rw [hg]
    change ψ (PowerSeries.C _) = ψ (PowerSeries.map _ _)
    rw [PowerSeries.map_C]
  · rw [hg]
    exact hle _
  · change ‖ψ (PowerSeries.map _ PowerSeries.X)‖ < 1
    rw [PowerSeries.map_X]
    refine hlt _ ?_
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _

end GlobalTheory.Ex
end

section

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_centred_at_prime :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (P : Ideal R), P.IsPrime → P ≠ ⊥ → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ∀ r ∈ P, ‖gam (algebraMap R K r)‖ < 1 := by
  intro R K _ _ _ _ _ _ _ P hP hP0
  obtain ⟨O, _, _, _, _, φ, hker, hcom⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) P (bot_lt_iff_ne_bot.2 hP0)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, h1, h2⟩ :=
    GlobalTheory.Ex.exists_complete_isAlgClosed_cExt O (FractionRing O)
  let ψ : R →+* C := (algebraMap (FractionRing O) C).comp ((algebraMap O (FractionRing O)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing O) C).injective.comp
      ((IsFractionRing.injective O (FractionRing O)).comp hφ)
  letI : Algebra R C := ψ.toAlgebra
  haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hψ
  let g : K →ₐ[R] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : ∀ r, g.toRingHom (algebraMap R K r) = ψ r := fun r => g.commutes r
  refine ⟨C, i1, i2, i3, i4, g.toRingHom, fun r => ?_, fun r hr => ?_⟩
  · rw [hg]
    exact h1 (φ r)
  · rw [hg]
    exact h2 (φ r) (by rw [← hcom] at hr; exact hr)

end GlobalTheory.Ex
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_finite_normal_ext_containing_algebraic_elements : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [CharZero R₁], IsIntegrallyClosed R₁ → ∀ (I : Type) [Finite I] (Φ : I → AlgebraicClosure (FractionRing R₁)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂) (j : FractionRing R₂ →+* AlgebraicClosure (FractionRing R₁)) (Φ₂ : I → FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ (∀ x, j (h' x) = algebraMap (FractionRing R₁) _ x) ∧ (∀ i, j (Φ₂ i) = Φ i) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (ga : FractionRing R₂ →+* F), ∃ σ : AlgebraicClosure (FractionRing R₁) →+* F, ∀ x, σ (j x) = ga x := by
  first | exact @GlobalTheory.OneBasis.exists_finite_normal_containing | exact GlobalTheory.OneBasis.exists_finite_normal_containing | (intros; apply GlobalTheory.OneBasis.exists_finite_normal_containing <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.arcData_psi_valuation_eq_half_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : O' →+* W) (u : W) (χ : Sp W ⟶ Y.X), Function.Injective f → Y.HasArcData a (maximalIdeal W) f u χ → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t) (e : a.D₀.X ≃+ P.D.toPre.X), ∀ (ϖ : W) (Q : P.D.toPre.X → ℤ) (w : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q → HasVal ϖ (algebraMap W (FractionRing W) u) w → ∀ y, Q (e y) = w * (a.be y y / 2) := by
  first | exact @GlobalTheory.ArcPsiVal.q_eq_of_hasArcData | exact GlobalTheory.ArcPsiVal.q_eq_of_hasArcData | (intros; apply GlobalTheory.ArcPsiVal.q_eq_of_hasArcData <;> assumption)
end
