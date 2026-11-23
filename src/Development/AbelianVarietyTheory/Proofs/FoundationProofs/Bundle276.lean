module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle274
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle270
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1Coboundary
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle191
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle273
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle272
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle964
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_val_mod (m v : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (m : ℂ)) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  conv_rhs => rw [← Nat.mod_add_div v m]
  push_cast
  have : 2 * Real.pi * Complex.I * ((v % m : ℕ) + (m : ℂ) * (v / m : ℕ)) / (m : ℂ) =
      2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ) + ((v / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_smul (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : ℤ_[l]) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) (h : Kum X l n x χ) :
    Kum X l n (c • x) (fun δ => PadicInt.toZModPow n c * χ δ) := by
  apply GlobalTheory.KZ.BettiB.kum_smul <;> assumption

end GlobalTheory.KZ.H3
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Lie

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {A : Over (Sp R)} [GrpObj A]
  {φ : A.left ⟶ G.left} {m : ℕ}

theorem exists_lift (h : IsGrpPullback A G x φ) (u : FramedFlatCoordinates.epsAt x ⟶ G) :
    ∃ v : epsR R ⟶ A, v.left ≫ φ = u.left :=
  let ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  ⟨e.symm u, by rw [← he, e.apply_symm_apply]⟩

theorem fibre_iff (h : IsGrpPullback A G x φ) {v : Fin m → (epsR R ⟶ A)} {u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ G)}
    (hu : ∀ i, (v i).left ≫ φ = (u i).left) :
    (∀ (c : Fin m → R) (w : epsR R ⟶ A) (w' : FramedFlatCoordinates.epsAt x ⟶ G), w.left ≫ φ = w'.left →
      (IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (u i).left) w')) ∧
    ∀ {O : Type} [CommRing O] {a : OAct O A} {b : OAct O G}, (∀ c, (a.act c).left ≫ φ = φ ≫ (b.act c).left) →
      ∀ χ : O →+* R, EigenvectorLieDegree.IsEigBasis a χ v ↔ FramedFlatCoordinates.IsEigenBasis b x χ u := by
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  obtain rfl : u = fun i => e (v i) := funext fun i => Over.OverMorphism.ext ((hu i).symm.trans (he _).symm)
  have one : (1 : Over.mk x ⟶ G).left = η[A].left ≫ φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ A), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have pr : ∀ u : Fin m → (epsR R ⟶ A), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin m → R) (w : epsR R ⟶ A),
      IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine ⟨fun c w w' hw => ?_, fun {O} _ a b hab χ => ?_⟩
  · obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
    exact hC c w
  have hP : ∀ v : epsR R ⟶ A, EigenvectorLieDegree.IsEigVec a χ v ↔ FramedFlatCoordinates.IsEigenTangent b x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[A]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ a.act c) = e v ≫ b.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hab, Category.assoc])
      rw [hR, E]
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

def EigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ) (m : ℕ)
    (v : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G)) (v' : Fin m → (FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ T.G)),
    FramedFlatCoordinates.IsEigenBasis T.act x (FramedFlatCoordinates.chr c τ j) v →
    (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) →
    FramedFlatCoordinates.IsEigenBasis T.act (spMap g ≫ x) (FramedFlatCoordinates.chr c τ (g.comp j)) v'

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

end GlobalTheory.FlatRow
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalUnitaryGlue

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem exists_on_finset (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ k : HA (Af F) σ J, (∀ v ∈ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v) ∧
      ∀ v ∉ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => map_one _⟩
  | insert a S ha ih =>
    obtain ⟨k, h1, h2⟩ := ih
    have s1 : mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F a) (extH σ J (sgV a) (sgV_mul a) (γ a)) = γ a :=
      mapH_extH_self σ J _ _ _ (fun y => Pi.single_eq_same a y) _
    have s2 : ∀ w, w ≠ a →
        mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (extH σ J (sgV a) (sgV_mul a) (γ a)) = 1 :=
      fun w hw => mapH_extH_zero σ J _ _ _ (fun y => Pi.single_eq_of_ne hw y) _
    refine ⟨extH σ J (sgV a) (sgV_mul a) (γ a) * k, fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [s1, h2 _ ha, mul_one]
      · rw [s2 v (fun e => ha (e ▸ hv)), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, s2 v hv.1, h2 v hv.2, one_mul]

theorem exists_of_finite (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : {v | γ v ≠ 1}.Finite) :
    ∃ k : HA (Af F) σ J, ∀ v, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v := by
  obtain ⟨k, h1, h2⟩ := exists_on_finset σ J γ h.toFinset
  refine ⟨k, fun v => ?_⟩
  by_cases hv : v ∈ h.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    simpa [eq_comm] using hv

end Gen

theorem exists_finite_adelic : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  intro D V γ h
  obtain ⟨k, hk⟩ := exists_of_finite D.sp.cm.sig V.gram γ h
  refine ⟨ofFin D.sp.cm V k, ?_, fun v => ?_⟩
  · exact congrArg (HA.mat _ _ _) (projInf_ofFin D.sp.cm V k)
  · have e : finMat D.sp.cm.sig V.gram (ofFin D.sp.cm V k) = (HA.mat _ _ _ k).1 :=
      congrArg (fun x => (HA.mat _ _ _ x).1) (projFin_ofFin D.sp.cm V k)
    rw [e, ← hk v]
    rfl

end GlobalTheory.LocalUnitaryGlue
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.UlSemisimple

theorem toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    (toGL g : Matrix (Fin 2) (Fin 2) ℝ).det = (g.det : ℝ) := by
  unfold toGL
  rw [dite_eq_right hg]
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]
  simp [Matrix.det_fin_two]

theorem slash_smul_pos (k : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] toGL g = c • (f ∣[k] toGL g) := by
  rw [ModularForm.smul_slash]
  congr 1
  simp only [UpperHalfPlane.σ]
  rw [if_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_det g hg.ne']; exact_mod_cast hg)]
  rfl

def ulLin (k : ℤ) (l : ℕ) (hl : 0 < l) : Module.End ℂ (ℍ → ℂ) where
  toFun := UlF k l
  map_add' f g := by simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [UlF, hkF, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => slash_smul_pos k _ ?_ c f
    simp [ulFam, Matrix.det_fin_two]
    exact_mod_cast hl

theorem ulLin_apply (k : ℤ) (l : ℕ) (hl : 0 < l) (F : ℍ → ℂ) : ulLin k l hl F = UlF k l F := rfl

def ChiLaw (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (F : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → F ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • F

def oldSp (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (hl : 0 < l) : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) k, ChiLaw N k χ ⇑f₁ ∧ ChiLaw N k χ ⇑f₂ ∧
    F = ⇑f₁ + ⇑f₂ ∣[k] toGL (dg l 1)}
  add_mem' := by
    rintro F G ⟨f₁, f₂, h₁, h₂, rfl⟩ ⟨g₁, g₂, h₁', h₂', rfl⟩
    refine ⟨f₁ + g₁, f₂ + g₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
    · rw [CuspForm.coe_add, SlashAction.add_slash, h₁ γ hγ, h₁' γ hγ, smul_add]
    · rw [CuspForm.coe_add, SlashAction.add_slash, h₂ γ hγ, h₂' γ hγ, smul_add]
    · rw [CuspForm.coe_add, CuspForm.coe_add, SlashAction.add_slash]; abel
  zero_mem' := ⟨0, 0, fun γ _ => by simp, fun γ _ => by simp, by simp⟩
  smul_mem' := by
    rintro c F ⟨f₁, f₂, h₁, h₂, rfl⟩
    have hd : 0 < (dg (l : ℤ) 1).det := by simp [dg, Matrix.det_fin_two]; exact_mod_cast hl
    refine ⟨c • f₁, c • f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
    · rw [CuspForm.coe_smul, ModularForm.SL_smul_slash, h₁ γ hγ, smul_comm]
    · rw [CuspForm.coe_smul, ModularForm.SL_smul_slash, h₂ γ hγ, smul_comm]
    · rw [CuspForm.coe_smul, CuspForm.coe_smul, slash_smul_pos k _ hd, smul_add]

theorem aeval_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (U : Module.End ℂ M) (O : Submodule ℂ M)
    (hU : ∀ x ∈ O, U x ∈ O) (p : ℂ[X]) (x : M) (hx : x ∈ O) : aeval U p x ∈ O := by
  have hpow : ∀ m : ℕ, ∀ y ∈ O, (U ^ m) y ∈ O := by
    intro m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hU _ (ih y hy)
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  exact O.sum_mem fun i _ => by rw [LinearMap.smul_apply]; exact O.smul_mem _ (hpow i x hx)

end GlobalTheory.HeckeFamilyMatrices.UlSemisimple


open GlobalTheory.HeckeFamilyMatrices.UlSemisimple in
theorem GlobalTheory.HeckeFamilyMatrices.ul_semisimple : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (α : ℂ), α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 2) →
  ∀ f : CuspForm (Lev N l) (k : ℤ), (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∀ n : ℕ, (fun F => UlF (k : ℤ) l F - α • F)^[n] ⇑f = 0 → UlF (k : ℤ) l ⇑f = α • ⇑f := by
  intro N l k hN hl hlN hk χ α hα1 hα2 f hf n hn
  have hl0 : 0 < l := hl.pos
  set U := ulLin (k : ℤ) l hl0 with hUdef
  set O := oldSp N l (k : ℤ) χ hl0 with hOdef
  have hUO : ∀ F ∈ O, U F ∈ O := by
    rintro F ⟨f₁, f₂, h₁, h₂, rfl⟩
    obtain ⟨g₁, g₂, hg₁, hg₂, he⟩ := (GlobalTheory.T.heckeUl_semisimple_on_lOldSpace N l k hN hl hlN hk χ α hα1 f₁ f₂ h₁ h₂).1
    exact ⟨g₁, g₂, hg₁, hg₂, he⟩
  set c : ℂ := χ l * (l : ℂ) ^ (k - 2) with hc
  have hcop : IsCoprime ((X - C α) ^ n) (X ^ 2 - C c) := by
    apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C α).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def]
    simpa [sub_eq_zero] using hα2
  obtain ⟨A, B, hAB⟩ := hcop
  have key : aeval U A (aeval U ((X - C α) ^ n) ⇑f) + aeval U B (aeval U (X ^ 2 - C c) ⇑f) = ⇑f := by
    have := congrArg (fun p => aeval U p ⇑f) hAB
    simpa only [map_add (f := _), map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply] using this
  have h1 : aeval U ((X - C α) ^ n) ⇑f = 0 := by
    rw [map_pow, map_sub, aeval_X, aeval_C, Module.End.pow_apply]
    convert hn using 2
    funext F
    simp [hUdef, ulLin_apply, Module.algebraMap_end_apply]
  have h2 : aeval U (X ^ 2 - C c) ⇑f ∈ O := by
    obtain ⟨f₁, f₂, h₁, h₂, he⟩ := GlobalTheory.T.hecke_Ul_sq_sub_mem_oldforms_Gamma1 N l k hN hl hlN hk χ f hf
    refine ⟨f₁, f₂, h₁, h₂, ?_⟩
    rw [← he, map_sub, aeval_C, map_pow, aeval_X, LinearMap.sub_apply, Module.algebraMap_end_apply,
      pow_two, Module.End.mul_apply]
    rfl
  have hfO : ⇑f ∈ O := by
    rw [← key, h1, map_zero, zero_add]
    exact aeval_mem U O hUO B _ h2
  obtain ⟨f₁, f₂, h₁, h₂, he⟩ := hfO
  have hss := (GlobalTheory.T.heckeUl_semisimple_on_lOldSpace N l k hN hl hlN hk χ α hα1 f₁ f₂ h₁ h₂).2 n
  rw [he] at hn ⊢
  exact hss hn

end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_galoisConjugate_modularFunction_someLevel : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω) (f : ℍ → ℂ), InR ε.range f → ∃ f' : ℍ → ℂ, InR ε.range f' ∧ ∀ h h' : HahnSeries ℚ Ω, IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  first | exact @GlobalTheory.FN.exists_conj_of_inR | exact GlobalTheory.FN.exists_conj_of_inR | (intros; apply GlobalTheory.FN.exists_conj_of_inR <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.geometric_level_h1_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong (p := p) n (a (g * h)) (a g + g (a h))) →
    ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * a g - o * ((lq g).val : Ω))) ∧
  (∀ o : Ω, IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) → Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => o * ((lq g).val : Ω)) → Cong (p := p) n ((p : Ω) ^ c * o) 0) := by
  exact @GlobalTheory.K5.Reb.h1_geometric_level_coboundary
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.jacquetModule_maximalParabolic_principalSeriesTypeEigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Cut ψ r → ∀ v ∈ twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eig_jacquet_zero | exact GlobalTheory.PsType.eig_jacquet_zero | (intros; apply GlobalTheory.PsType.eig_jacquet_zero <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisMReal

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (fun n => c * a n) = fun τ => c * qs a τ := by
  funext τ
  unfold qs
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

theorem pet_smul_right (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ h (fun τ => c * f τ) = c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  ring

theorem pet_smul_left (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ (fun τ => c * h τ) f = conj c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [map_mul]
  ring

theorem eig_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g →
    q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  intro k N q χ g hk hN hg hq hqN
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight N hN
  have hT : To k (ch χ q) q g = fun n => g q * g n := hg.eig q hq hqN
  have hadj := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k N N q χ ρ g g hk hN dvd_rfl hq hqN hρ hg.cf hg.cf.1
  have hne : g ≠ 0 := by
    intro h0
    have := hg.one
    rw [h0] at this
    simp at this
  have hP := GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm k N N χ ρ g hk hN dvd_rfl hρ hg.cf hne
  rw [hT, qs_smul, pet_smul_right, pet_smul_left] at hadj
  exact mul_right_cancel₀ hP (hadj.trans (by ring) : g q * pet k ρ (qs g) (qs g) = ch χ q * conj (g q) * pet k ρ (qs g) (qs g))

end GlobalTheory.EisMReal
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.kummerCompletion_no_prime_torsion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (x : X.Khat l), (l : ℤ_[l]) • x = 0 → x = 0 := by
  first | exact @GlobalTheory.KZ.BettiB.khat_no_l_torsion | exact GlobalTheory.KZ.BettiB.khat_no_l_torsion | (intros; apply GlobalTheory.KZ.BettiB.khat_no_l_torsion <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.kummerCocycle_value_expansion_eq_logDeriv_smul : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (cw : ℤ → Ω) (w w' r : Ω), Ev ψ cw w w' → w ≠ 0 → IsInt (p := p) w⁻¹ → r ^ (p ^ n) = w →
  ∀ a lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) r a → IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * (w' / w) * ((lq g).val : Ω)) := by
  first | exact @GlobalTheory.K5.GeoKummer.geo_cob | exact GlobalTheory.K5.GeoKummer.geo_cob | (intros; apply GlobalTheory.K5.GeoKummer.geo_cob <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.integral_series_of_common_divisor_line_products : ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (e Ψ A B : PowerSeries ℂ_[p]) (y : Fin m → ℂ_[p]) (y' : Fin n → ℂ_[p]), BddSer e → BddSer Ψ → BddSer A → BddSer B → PowerSeries.constantCoeff Ψ = 1 → Ψ * A = (∏ i, lineSer e (y i)) ^ 2 → Ψ * B = ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → IntSer Ψ := by
  first | exact @GlobalTheory.EvenTheta.intSer_of_common_divisor | exact GlobalTheory.EvenTheta.intSer_of_common_divisor | (intros; apply GlobalTheory.EvenTheta.intSer_of_common_divisor <;> assumption)
end
