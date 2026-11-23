module

public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle109
public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle115
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle116
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Mathlib.FieldTheory.Galois.Infinite
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

theorem _root_.GlobalTheory.T.exists_rootOfUnity_lift_from_residueField : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m → ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  first | exact @GlobalTheory.TameLift.exists_lift | exact GlobalTheory.TameLift.exists_lift | (intros; apply GlobalTheory.TameLift.exists_lift <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem invariants_finExt : ∀ (l : ℕ) [Fact l.Prime], ∀ (K : FinExt l) (x : ℂ_[l]), (∀ g ∈ GK K, Per.σC g x = x) → ∃ y ∈ K.1, ((y : Om l) : ℂ_[l]) = x := by
  intro l _ K x hx
  have h := GlobalTheory.T.ax_sen_tate_complex_padic_fixed_closure l (GK K) x hx
  have hset : {y : Om l | ∀ g ∈ GK K, g y = y} = (K.1 : Set (Om l)) := by
    ext y
    have h1 := InfiniteGalois.fixedField_fixingSubgroup K.1
    constructor
    · intro hy
      have : y ∈ IntermediateField.fixedField K.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        exact hy
      rwa [h1] at this
    · intro hy g hg
      exact (IntermediateField.mem_fixingSubgroup_iff K.1 g).1 hg y hy
  rw [hset] at h
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] K.1.toSubalgebra.toSubmodule := K.2
  have hc : IsComplete (K.1 : Set (Om l)) :=
    Submodule.complete_of_finiteDimensional (𝕜 := ℚ_[l]) K.1.toSubalgebra.toSubmodule
  have hc2 : IsComplete ((fun y : Om l => (y : ℂ_[l])) '' (K.1 : Set (Om l))) :=
    (isComplete_image_iff (UniformSpace.Completion.isUniformInducing_coe (Om l))).2 hc
  rw [hc2.isClosed.closure_eq] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, hy, rfl⟩

end GlobalTheory.MemLoc
end

section

noncomputable section

namespace GlobalTheory.Mem.R3.DefLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

structure BlockBaseChange (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (ℓ : Lvl K G) (ℓ' : Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) : Prop where

  forms : ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
    Cᴴ * B'.S.H * C = B.S.H.map φ ∧
    (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
    B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
    B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K)))

  X : ∀ χ' : G' → K', χ' ∈ ℓ'.X ↔ ∃ χ ∈ ℓ.X, χ' = fun g => φ (χ (e.symm g))

  P : ℓ'.P = ℓ.P.map e.toMonoidHom

  ψ : ∀ h : ℓ.P, ((ℓ'.ψ ⟨e h, P ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : K'ˣ) : K') = φ (ℓ.ψ h : K)

end GlobalTheory.Mem.R3.DefLatBC

end
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_conj_inertia_tameChar_other_place : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TameMove.tameRep_move | exact GlobalTheory.TameMove.tameRep_move | (intros; apply GlobalTheory.TameMove.tameRep_move <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.tameInertia_representative_residue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime], IsPlaceOver (F := E) A P → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), σ ∈ Ine (F := E) A → IsGenSys ζ → TameCoupled A κ σ ζ → (∀ A' : ValuationSubring Ω, IsPlaceOver (F := E) A' P → σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A) → ∀ u : 𝓞 E, NX.TameRep P 1 σ u → ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧ algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  first | exact @GlobalTheory.tameRep_residue | exact GlobalTheory.tameRep_residue | (intros; apply GlobalTheory.tameRep_residue <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.FrameBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem lieBasis_iff {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x : Sp S ⟶ X) (G' : Over (Sp S)) [GrpObj G']
    (φ : G'.left ⟶ t.G.left) (hp : IsGrpPullback G' t.G x φ) :
    (∀ w : (Sp (DualNumber S) ⟶ t.G.left), IsTanAtG t x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧
    ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ ((∀ i, IsTanAtG t x ((v i).left ≫ φ)) ∧
      ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x (fun i => (v i).left ≫ φ) a w) := by
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left,
      w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAtG t x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAtG t x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (GlobalTheory.Frames.spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x ⟶ t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

theorem tanBasis_baseChange {X : Scheme.{0}} (t : SAB H X) {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (x : Sp S ⟶ X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hv' : ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x v a w) :
    (∀ i, IsTanAtG t (spMap φ ≫ x) (spMap (dualMap φ) ≫ v i)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ x) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) a w := by
  have := t.semi.comm
  have := t.semi.smooth
  have h₁ := isGrpPullback_pullback t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := lieBasis_iff t x _ _ h₁
  obtain ⟨-, b₃⟩ := lieBasis_iff t _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv i)
  have hb : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hv'⟩
  have hs : Smooth ((Over.pullback x).obj t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
      spMap (dualMap φ) ≫ v i := fun i => by
    rw [← Category.assoc, hu', e, Category.assoc, hu]
  refine ⟨fun i => e' i ▸ key.1 i, ?_⟩
  rw [← funext e']
  exact key.2

end GlobalTheory.LocM.FrameBase
end
end

section

open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.isIntegral_of_divisible_characters : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] (B₀ B₁ : Type) [CommRing B₀] [Algebra ↥(intO C) B₀] [Module.Finite ↥(intO C) B₀] [CommRing B₁] [Algebra C B₁] [Algebra ↥(intO C) B₁] [IsScalarTower ↥(intO C) C B₁] (j : B₀ →ₐ[↥(intO C)] B₁) (x : B₀) (q : ↥(intO C)), q ≠ 0 → (∀ χ : B₀ →ₐ[↥(intO C)] ↥(intO C), q ∣ χ x) → IsIntegral ↥(intO C) (((q : C)⁻¹) • j x) := by
  first | exact @GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul | exact GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul | (intros; apply GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul <;> assumption)
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.absIrrSub_of_isIrrSub_span_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W → IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) → AbsIrrSub ρ W := by
  first | exact @GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | exact GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | (intros; apply GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.SqLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

abbrev sq (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {x : X} {j : L.ι} (h : x ∈ L.U j) : x ∈ (sq L).U (fun _ => j) :=
  Set.mem_iInter.2 fun _ => h

theorem gm_sq_g (f : Y ⟶ X) (y : Y) {j j' : L.ι} (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y ((sq L).U (fun _ => j) ⊓ (sq L).U (fun _ => j')) ((sq L).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ (2 : ℤ) := by
  refine (gm_linComb L (fun _ => 𝟙 X) (fun _ => 2) f y _ _ (mem_sq hj) (mem_sq hj')).trans ?_
  rw [Fintype.prod_unique, Category.comp_id]

def gq (w : LB.Iso (sq L') ((sq L).pull F)) (f : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gw w f y (fun _ => j) (fun _ => k)

theorem gq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (f : Y ⟶ X') (y : Y) {j j' : L.ι} {k k' : L'.ι}
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gq w f y j k = gm (f ≫ F) y _ (L.g j j') ^ (2 : ℤ) * (gm f y _ (L'.g k k') ^ (2 : ℤ))⁻¹ * gq w f y j' k' := by
  rw [gq, gq, hw Y f y _ _ _ _ (mem_sq hj) (mem_sq hj') (mem_sq hk) (mem_sq hk'), gm_sq_g (f ≫ F) y hj hj',
    gm_sq_g f y hk hk']

def pq (w : LB.Iso (sq L') ((sq L).pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι)
    (q : K → L'.ι) : (Z.presheaf.stalk z)ˣ := ∏ k, gq w (r ≫ φ' k) z (p k) (q k) ^ ε k

theorem trF_two {M : LB X} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (j j' : K → M.ι) :
    trF φ (fun k => 2 * ε k) r z j j' = trF φ ε r z j j' ^ (2 : ℤ) := by
  rw [trF, trF, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

theorem pq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pq w φ' ε r z p q = trF (fun k => φ' k ≫ F) (fun k => 2 * ε k) r z p p' *
      (trF φ' (fun k => 2 * ε k) r z q q')⁻¹ * pq w φ' ε r z p' q' := by
  rw [trF_two, trF_two, pq, pq, trF, trF, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gq_trans hw (r ≫ φ' k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  rw [smul_add, smul_add, smul_comm (ε k) (2 : ℤ), smul_neg, smul_comm (ε k) (2 : ℤ)]

theorem exists_pq (w : LB.Iso (sq L') ((sq L).pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (p : K → L.ι) (q : K → L'.ι) :
    ∃ u : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q → gm r z _ u = pq w φ' ε r z p q := by
  have le : ∀ k, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      φ' k ⁻¹ᵁ (((sq L).pull F).U (fun _ => fun _ => p k) ⊓ (sq L').U (fun _ => q k)) := fun k y hy =>
    ⟨mem_pull.2 (mem_sq (Set.mem_iInter.1 hy.1 k)), mem_sq (Set.mem_iInter.1 hy.2 k)⟩
  exact ⟨∏ k, res (le k) (pullU (φ' k) _ (w.s (fun _ => fun _ => p k, fun _ => q k))) ^ ε k, fun Z r z hz =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
      ((gm_res r z (le k) hz _).trans (gm_pull r (φ' k) z _ (le k hz) _))))⟩

theorem exists_sq_up {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
  choose u hu using fun p q => exists_pq w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
    intro p
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ (u p q * res inf_le_right (a.s q) ^ 2) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 :=
      fun Z r z q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (hu p q Z r z hz)
        ((map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hz _))))
    obtain ⟨s, hs⟩ := glue_unit _ (fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_left)
      (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) (fun q => u p q * res inf_le_right (a.s q) ^ 2)
      (fun q q' y hy => by
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, pq_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hL _ _ (𝟙 Y) y hy.1.1, trF_two, gen_trans ha (𝟙 Y) y hy.1.2 hy.2.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
        abel)
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hz s).symm.trans ((congrArg (gm r z _) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (hs j _ (𝟙 Y) y q hj m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hj' m)).symm)
  rw [pq_trans hw φ' ε (𝟙 Y) y hj hj' m m, trF_self hL' _ _ (𝟙 Y) y m, inv_one, _root_.mul_one, _root_.mul_assoc]

theorem exists_sq_gen : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  intro X X' Y L L' F hL hL' w hwg K _ φ' ε a ha
  obtain ⟨t, ht, hv⟩ := exists_sq_up ((isGen_iff w).1 hwg) hL hL' a ha
  refine ⟨t, ht, fun Z z ψ J J' => ∏ k, gq w (ψ k) z (J (ψ k ≫ F)) (J' (ψ k)) ^ ε k, fun Z r z J J' hJ hJ' => ?_⟩
  refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans ?_
  simp only [pq, Category.assoc]
  rfl

end GlobalTheory.SqLB
end
end
