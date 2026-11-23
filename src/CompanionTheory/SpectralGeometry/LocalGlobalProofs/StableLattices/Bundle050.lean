module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle049
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle019
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.CasimirDiagonalSum : CasDS := by
  first | exact @GlobalTheory.CompanionTheory.CasimirDS.casDS | exact GlobalTheory.CompanionTheory.CasimirDS.casDS | (intros; apply GlobalTheory.CompanionTheory.CasimirDS.casDS <;> assumption)
end

section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFarReg

open Finset
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

lemma kRel_of_glRel {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) : CompanionTheory.D.DSIC.KRel ε E :=
  fun a b c d _ _ => hE a b c d

lemma kUnit_of_isUnitary {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E) : CompanionTheory.D.DSIC.KUnit ε E := by
  intro a b he x y
  rw [hU a b x y]
  simp [Formalism.REAL.sgn, he]

lemma dominant_of_kHighest {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hF : CompanionTheory.D.DSIC.KRel ε E) (hU : CompanionTheory.D.DSIC.KUnit ε E)
    {μ : Fin n → ℝ} {u : V} (hu : u ≠ 0) (hh : KHighest ε E μ u) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    μ b ≤ μ a := by
  have h := GlobalTheory.CompanionTheory.KWeightMajor.norm_identity hF hU he hh.1
  rw [hh.2 a b hab he, norm_zero] at h
  have hp : 0 < ‖u‖ ^ 2 := by have := norm_pos_iff.2 hu; positivity
  by_contra hc
  push Not at hc
  have : 0 < (μ b - μ a) * ‖u‖ ^ 2 := mul_pos (by linarith) hp
  have := sq_nonneg ‖E b a u‖
  nlinarith

lemma two_rhoC_int (ε : Fin n → Bool) (a : Fin n) : ∃ m : ℤ, ((2 : ℝ) • rhoC ε) a = m := by
  refine ⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
  simp only [Pi.smul_apply, rhoC, smul_eq_mul]
  push_cast
  ring

lemma vNormSq_nat (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : ∀ a, ∃ m : ℤ, μ a = m) :
    ∃ k : ℕ, vNormSq ε μ = k := by
  choose m hm using hμ
  choose r hr using two_rhoC_int ε
  refine ⟨∑ a, ((m a + r a) ^ 2).toNat, ?_⟩
  have h : ∀ a, (((m a + r a) ^ 2).toNat : ℝ) = (μ a + ((2 : ℝ) • rhoC ε) a) ^ 2 := by
    intro a
    have h0 : (((m a + r a) ^ 2).toNat : ℤ) = (m a + r a) ^ 2 := Int.toNat_of_nonneg (sq_nonneg _)
    have h1 : (((m a + r a) ^ 2).toNat : ℝ) = (((m a + r a) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h0
    rw [h1, hm a, hr a]
    push_cast
    ring
  rw [Nat.cast_sum]
  simp only [vNormSq, PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [h a, sq]

theorem lktExists : LKTExists := by
  classical
  intro n ε V _ _ E hE hV hU hfin hint
  have hF : CompanionTheory.D.DSIC.KRel ε E := kRel_of_glRel hE
  have hK : CompanionTheory.D.DSIC.KUnit ε E := kUnit_of_isUnitary hU
  have hintK : ∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → ∀ a, ∃ m : ℤ, μ a = m :=
    fun μ x hx hh => hint μ x hx hh.1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨S, hfd, hS, hxS⟩ := hfin x
  obtain ⟨y, -, hy0, ν, hy⟩ := Formalism.REAL.highestWeightExists_holds V n ε E S hfd hF hK hS
    (fun h => hx (by simpa [h] using hxS))
  have hex : ∃ k : ℕ, ∃ (μ : Fin n → ℝ) (w : V), w ≠ 0 ∧ KHighest ε E μ w ∧ vNormSq ε μ = k := by
    obtain ⟨k, hk⟩ := vNormSq_nat ε (hintK ν y hy0 hy)
    exact ⟨k, ν, y, hy0, hy, hk⟩
  obtain ⟨γ, u, hu, hγ, hk⟩ := Nat.find_spec hex
  refine ⟨γ, u, hu, hγ, ?_, hintK γ u hu hγ, fun a b hab he => dominant_of_kHighest hF hK hu hγ hab he⟩
  intro μ w hw hμ
  obtain ⟨k, hk'⟩ := vNormSq_nat ε (hintK μ w hw hμ)
  rw [hk, hk']
  exact_mod_cast Nat.find_min' hex ⟨μ, w, hw, hμ, hk'⟩

end GlobalTheory.CompanionTheory.RgExhFarReg
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigCover

theorem exists_gen_of_chart {Y P : Scheme.{0}} {M : LB P} (hM : M.IsLB) (f : Y ⟶ P) (i : M.ι)
    (hf : ∀ y, f y ∈ M.U i) : ∃ t : LB.Gen (M.pull f), t.IsGen := by
  have le (J : (M.pull f).ι) : (M.pull f).U J ≤ f ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U i) :=
    fun y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => Units.map (f.appLE _ _ (le J)).hom.toMonoidHom (M.g (J PUnit.unit) i)⟩, ?_⟩
  intro J J'
  let j := J PUnit.unit
  let k := J' PUnit.unit
  let U := (M.pull f).U J ⊓ (M.pull f).U J'
  let V := M.U j ⊓ M.U k ⊓ M.U i
  have hUV : U ≤ f ⁻¹ᵁ V := fun y hy => ⟨⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩, hf y⟩
  let pullToU := Units.map (f.appLE V U hUV).hom.toMonoidHom
  have pull_res {A : P.Opens} (h : V ≤ A) (a : Γ(P, A)ˣ) :
      pullToU (res h a) = Units.map (f.appLE A U (hUV.trans (f.preimage_mono h))).hom.toMonoidHom a := by
    apply Units.ext
    exact congrArg (fun q => q.hom a.val) (f.map_appLE hUV (homOfLE h).op)
  have res_pull {A : P.Opens} {B : Y.Opens} (h : B ≤ f ⁻¹ᵁ A) (h' : U ≤ B) (a : Γ(P, A)ˣ) :
      res h' (Units.map (f.appLE A B h).hom.toMonoidHom a) = Units.map (f.appLE A U (h'.trans h)).hom.toMonoidHom a := by
    apply Units.ext
    exact congrArg (fun q => q.hom a.val) (f.appLE_map h (homOfLE h').op)
  have transition : (M.pull f).g J J' = pullToU (res inf_le_left (M.g j k)) := by
    show (∏ _ : PUnit, (res _ (pullU f _ (M.g j k))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one, pull_res]
    rfl
  change res (_ : U ≤ (M.pull f).U J) (Units.map (f.appLE _ _ (le J)).hom.toMonoidHom (M.g j i)) =
    (M.pull f).g J J' * res (_ : U ≤ (M.pull f).U J') (Units.map (f.appLE _ _ (le J')).hom.toMonoidHom (M.g k i))
  calc
    _ = pullToU (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (M.g j i)) :=
      (res_pull (le J) inf_le_left _).trans (pull_res _ _).symm
    _ = pullToU (res inf_le_left (M.g j k)) *
        pullToU (res (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (M.g k i)) := by
      rw [← map_mul]
      exact congrArg pullToU (hM.cocycle j k i).symm
    _ = _ := congrArg₂ (· * ·) transition.symm
      ((pull_res _ _).trans (res_pull (le J') inf_le_right _).symm)

theorem exists_flat_cover_triv : ∀ {P : Scheme.{0}} (M : LB P), M.IsLB → ∃ (Z : Scheme.{0}) (g : Z ⟶ P),
    Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧ Triv (M.pull g) := by
  intro P M hM
  let D : M.ι → Scheme.{0} := fun i => (M.U i).toScheme
  let g : ∐ D ⟶ P := Sigma.desc fun i => (M.U i).ι
  have hι : ∀ i, Sigma.ι D i ≫ g = (M.U i).ι := fun i => Sigma.ι_comp_desc _ i
  refine ⟨∐ D, g, ?_, ?_, ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    have hf : ∀ i : M.ι, Flat (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @Flat) (sigmaOpenCover D) hf
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    have hf : ∀ i : M.ι, LocallyOfFinitePresentation (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) (sigmaOpenCover D) hf
  · refine ⟨fun x => ?_⟩
    obtain ⟨i, hi⟩ := exists_chart hM x
    let x' : D i := ⟨x, hi⟩
    refine ⟨Sigma.ι D i x', ?_⟩
    have e : (Sigma.ι D i ≫ g) x' = x := by rw [hι]; rfl
    exact e
  · let Z := ∐ D
    let σ (s : M.ι) : D s ⟶ Z := Sigma.ι D s
    have cover (y : Z) : ∃ s, y ∈ (σ s).opensRange := by
      obtain ⟨s, x, rfl⟩ := (sigmaOpenCover D).exists_eq y
      exact ⟨s, x, rfl⟩
    have sections (U : Z.Opens) (V : ∀ s, (D s).Opens) (hV : ∀ s, V s = σ s ⁻¹ᵁ U) :
        Function.Bijective (fun a : Γ(Z, U)ˣ => fun s =>
          Units.map ((σ s).appLE U (V s) (hV s).le).hom.toMonoidHom a) := by
      have hv : V = fun s => σ s ⁻¹ᵁ U := funext hV
      subst V
      simp only [Scheme.Hom.appLE_eq_app]
      let E (s : M.ι) := (σ s).opensRange ⊓ U
      let e (s : M.ι) := IsOpenImmersion.ΓIso (σ s) U
      have hc : U ≤ ⨆ s, E s := fun y hy => by
        obtain ⟨s, hs⟩ := cover y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨s, hs, hy⟩
      have restrict (a : Γ(Z, U)) (s : M.ι) :
          (e s).hom.hom (((σ s).app U).hom a) =
            (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom a :=
        congrArg (fun q => q.hom a) (IsOpenImmersion.app_ΓIso_hom (σ s) U)
      have compatible (a : ∀ s, Γ(Z, E s)) : TopCat.Presheaf.IsCompatible Z.sheaf.1 E a := by
        intro s s'
        by_cases he : s = s'
        · subst s'
          rfl
        · apply TopCat.Presheaf.section_ext Z.sheaf (E s ⊓ E s')
          intro y hy
          have hd := disjoint_iff.1 (disjoint_opensRange_sigmaι D s s' he)
          have hm : y ∈ (σ s).opensRange ⊓ (σ s').opensRange := ⟨hy.1.1, hy.2.1⟩
          rw [hd] at hm
          exact hm.elim
      have ext_sections (a b : Γ(Z, U))
          (h : ∀ s, (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom a =
            (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom b) : a = b :=
        Z.sheaf.eq_of_locally_eq' E U (fun _ => homOfLE inf_le_right) hc a b h
      constructor
      · intro a b hab
        apply Units.ext
        apply ext_sections
        intro s
        rw [← restrict, ← restrict]
        exact congrArg (fun u : Γ(D s, σ s ⁻¹ᵁ U)ˣ => (e s).hom.hom u.val)
          (congrFun hab s)
      · intro a
        let b (s : M.ι) : Γ(Z, E s)ˣ := Units.map (e s).hom.hom.toMonoidHom (a s)
        obtain ⟨u, hu, _⟩ := Z.sheaf.existsUnique_gluing' E U (fun _ => homOfLE inf_le_right) hc
          (fun s => (b s).val) (compatible _)
        obtain ⟨v, hv, _⟩ := Z.sheaf.existsUnique_gluing' E U (fun _ => homOfLE inf_le_right) hc
          (fun s => (b s).inv) (compatible _)
        have huv : u * v = 1 := by
          apply ext_sections
          intro s
          simp only [map_mul, map_one]
          exact (congrArg₂ (· * ·) (hu s) (hv s)).trans (b s).val_inv
        refine ⟨⟨u, v, huv, (mul_comm v u).trans huv⟩, funext fun s => ?_⟩
        apply Units.ext
        apply (e s).commRingCatIsoToRingEquiv.injective
        exact (restrict u s).trans (hu s)
    let L := M.pull g
    let Ls (s : M.ι) := M.pull (σ s ≫ g)
    have localGen (s : M.ι) : ∃ t : LB.Gen (Ls s), t.IsGen := by
      refine exists_gen_of_chart hM (σ s ≫ g) s fun y => ?_
      change (Sigma.ι D s ≫ g) y ∈ M.U s
      rw [hι]
      exact y.2
    choose t ht using localGen
    have charts (s : M.ι) (J : L.ι) : (Ls s).U J = σ s ⁻¹ᵁ L.U J := by
      ext y
      exact mem_pull.trans (mem_pull (F := g)).symm
    let pullOn (s : M.ι) (A : Z.Opens) (B : (D s).Opens) (h : B ≤ σ s ⁻¹ᵁ A) :=
      Units.map ((σ s).appLE A B h).hom.toMonoidHom
    have glue (J : L.ι) : ∃ a : Γ(Z, L.U J)ˣ,
        ∀ s, pullOn s _ _ (charts s J).le a = (t s).s J := by
      obtain ⟨a, ha⟩ := (sections (L.U J) (fun s => (Ls s).U J) (fun s => charts s J)).2
        (fun s => (t s).s J)
      exact ⟨a, fun s => congrFun ha s⟩
    choose a ha using glue
    refine ⟨⟨a⟩, ?_⟩
    intro J J'
    let U := L.U J ⊓ L.U J'
    let V (s : M.ι) := (Ls s).U J ⊓ (Ls s).U J'
    have hV (s : M.ι) : V s = σ s ⁻¹ᵁ U := by
      change (Ls s).U J ⊓ (Ls s).U J' = _
      rw [charts, charts]
      rfl
    apply (sections U V hV).1
    funext s
    change pullOn s U (V s) (hV s).le (res inf_le_left (a J)) =
      pullOn s U (V s) (hV s).le (L.g J J' * res inf_le_right (a J'))
    have pull_restrict {A : Z.Opens} {B : (D s).Opens} (h : U ≤ A) (h' : V s ≤ B)
        (hB : B ≤ σ s ⁻¹ᵁ A) (b : Γ(Z, A)ˣ) :
        pullOn s U (V s) (hV s).le (res h b) = res h' (pullOn s A B hB b) := by
      apply Units.ext
      exact congrArg (fun q => q.hom b.val)
        (((σ s).map_appLE (hV s).le (homOfLE h).op).trans
          ((σ s).appLE_map hB (homOfLE h').op).symm)
    have transitions : pullOn s U (V s) (hV s).le (L.g J J') = (Ls s).g J J' := by
      let j := J PUnit.unit
      let k := J' PUnit.unit
      show pullOn s U (V s) (hV s).le
          (∏ _ : PUnit, res _ (pullU g _ (M.g j k)) ^ (1 : ℤ)) =
        ∏ _ : PUnit, res _ (pullU (σ s ≫ g) _ (M.g j k)) ^ (1 : ℤ)
      simp only [Fintype.prod_unique, zpow_one]
      apply Units.ext
      exact congrArg (fun q => q.hom (M.g j k).val)
        (Scheme.Hom.appLE_comp_appLE (σ s) g _ U (V s) _ (hV s).le)
    rw [map_mul, pull_restrict inf_le_left inf_le_left (charts s J).le,
      pull_restrict inf_le_right inf_le_right (charts s J').le, ha, ha, transitions]
    exact ht s J J'

end GlobalTheory.CompanionTheory.RigCover
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem not_acyclic_cechLB_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X)
    (hN : N.IsLB) (hT : Triv N) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hc : ⨆ i, D i = ⊤) : ¬ (cechLB f N D).Acyclic := by
  intro hac
  obtain ⟨t, ht⟩ := hT
  let σ : LB.Sec N := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  have h0 := hac 0
  rw [cochainComplex_exactAt_zero_iff, cechLB_d _ _ _ 0] at h0
  let x : (secCube f N D).obj ∅ := SecOnR.of f N _ (GlobalTheory.LB.ofSec σ _)
  have hx : Cube.aug (secCube f N D) x = 0 := h0 ((Cube.d_aug _ _).trans (map_zero _).symm)
  obtain ⟨p⟩ := ‹Nonempty X›
  obtain ⟨i, hi⟩ : ∃ i, p ∈ D i := by
    have hp : p ∈ ⨆ i, D i := by rw [hc]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨c, hcp⟩ : ∃ c, p ∈ N.U c := by
    have hp : p ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  have e := congrFun hx ⟨{i}, Finset.card_singleton i⟩
  have e₂ := congrArg (fun y : SecOnR f N (⨅ j ∈ ({i} : Finset κ), D j) => SecOnR.coord y c) e
  have hpW : p ∈ (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c := by
    refine ⟨?_, hcp⟩
    simpa using hi
  have hu : IsUnit (rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c)
      (t.s c).val) := (t.s c).isUnit.map (rs X inf_le_right)
  have e₃ : rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c) (t.s c).val = 0 := by
    let y : SecOnR f N (⨅ j ∈ (∅ : Finset κ), D j) := x
    have e₄ : rs X (inf_le_inf_right _ (iInf_le_iInf_of_subset D (Finset.empty_subset {i})))
        (SecOnR.coord y c) = 0 := e₂
    have e₅ : SecOnR.coord y c = rs X inf_le_right (t.s c).val := GlobalTheory.LB.coord_ofSec _ _ _
    rw [e₅, rs_rs] at e₄
    exact e₄
  rw [e₃] at hu
  have hu' := hu.map (X.presheaf.germ _ p hpW).hom
  rw [map_zero] at hu'
  exact not_isUnit_zero hu'

end GlobalTheory.CompanionTheory.PointSurjectivity
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem over_affineOpen_of_isPullback : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T)
    (H : IsPullback p q a b) {V : T.Opens} (hV : IsAffineOpen V) {κ : Type} [LinearOrder κ] [Fintype κ]
    (D : κ → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (G : LB Z) (hG : G.IsLB), (∀ i, IsAffineOpen (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V)) ∧
    ∃ (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec Γ(T, V)) (E : κ → Y.Opens),
      IsPullback π f q hV.fromSpec ∧ (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ ∧
      Nonempty (cechLB (f ≫ hV.fromSpec ≫ b) (G.pull π) E ≅ cechLB (p ≫ a) G fun i => p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) := by
  intro k _ X T Z a b p q H V hV κ _ _ D hD hc G hG
  let π := pullback.fst q hV.fromSpec
  let f := pullback.snd q hV.fromSpec
  have H₁ : IsPullback π f q hV.fromSpec := IsPullback.of_hasPullback _ _
  have H' : IsPullback f (π ≫ p) (hV.fromSpec ≫ b) a := H₁.flip.paste_vert H.flip
  have hq : IsAffineHom (π ≫ p) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H' inferInstance
  have hr : π.opensRange = q ⁻¹ᵁ V := by
    ext1
    rw [Scheme.Hom.coe_opensRange]
    erw [Scheme.Pullback.range_fst]
    rw [hV.range_fromSpec]
    rfl
  have hE (i : κ) : π ⁻¹ᵁ (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) = (π ≫ p) ⁻¹ᵁ D i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : κ) : IsAffineOpen ((π ≫ p) ⁻¹ᵁ D i) := (hD i).preimage _
  refine ⟨fun i => ?_, _, π, f, fun i => π ⁻¹ᵁ (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V), H₁,
    fun i => (congrArg IsAffineOpen (hE i)).mpr (hA i), ?_, ?_⟩
  · have h := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h
  · simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  · have e : f ≫ hV.fromSpec ≫ b = π ≫ p ≫ a := by
      rw [← H₁.w_assoc, H.w]
    rw [e]
    exact cechLB_pull_iso_of_isOpenImmersion k _ _ G _ π κ _ hG fun i => hr ▸ inf_le_right

end GlobalTheory.CompanionTheory.PointSurjectivity
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem isPullback_snd_lift_fst_snd_comp {S : Scheme.{0}} (A X Y : Over S) (q : X ⟶ Y) :
    IsPullback (snd A X).left (lift (fst A X) (snd A X ≫ q)).left q.left (snd A Y).left := by
  have hX : IsPullback (fst A X).left (snd A X).left A.hom X.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom X.hom
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom Y.hom
  have e₁ : (lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left = (fst A X).left := by
    rw [← Over.comp_left, lift_fst]
  have e₂ : (lift (fst A X) (snd A X ≫ q)).left ≫ (snd A Y).left = (snd A X).left ≫ q.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hout : IsPullback ((lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left) (snd A X).left
      A.hom (q.left ≫ Y.hom) := by
    rw [e₁, Over.w q]
    exact hX
  exact (IsPullback.of_right hout e₂ hY).flip

theorem lift_fst_snd_comp_flat_lfp_surjective :
    ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    Flat (lift (fst A X) (snd A X ≫ q)).left ∧ LocallyOfFinitePresentation (lift (fst A X) (snd A X ≫ q)).left ∧
      Surjective (lift (fst A X) (snd A X ≫ q)).left := by
  intro S A X Y _ _ q hf hl hs
  have h := isPullback_snd_lift_fst_snd_comp A X Y q
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) h hf,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hl,
    MorphismProperty.of_isPullback (P := @Surjective) h hs⟩

end GlobalTheory.CompanionTheory.RigDesc
end
