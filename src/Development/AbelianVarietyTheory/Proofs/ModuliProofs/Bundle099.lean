module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.AmpleBasis

open SectionRing

variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)

def Extends (N : ℕ) (D : X.Opens) (t : Fam p L) (f : Γ(X, D)) (e : ℕ) : Prop :=
  ∃ σ ∈ secs p L (N * e), ∀ k,
    resG X (inf_le_right : D ⊓ chart L k ≤ _) (evalFam p L k σ) =
      resG X (inf_le_left : D ⊓ chart L k ≤ _) f *
        resG X (inf_le_right : D ⊓ chart L k ≤ _) (evalFam p L k t) ^ e

variable {p L} {N : ℕ} {D : X.Opens} {t : Fam p L}

theorem Extends.mul {f g : Γ(X, D)} {e e' : ℕ} (hf : Extends p L N D t f e)
    (hg : Extends p L N D t g e') : Extends p L N D t (f * g) (e + e') := by
  obtain ⟨σ, hσ, h⟩ := hf
  obtain ⟨τ, hτ, h'⟩ := hg
  refine ⟨σ * τ, ?_, fun k => ?_⟩
  · rw [mul_add]
    exact SetLike.GradedMul.mul_mem hσ hτ
  · simp only [map_mul]
    rw [h k, h' k, pow_add]
    ring

theorem Extends.add {f g : Γ(X, D)} {e : ℕ} (hf : Extends p L N D t f e)
    (hg : Extends p L N D t g e) : Extends p L N D t (f + g) e := by
  obtain ⟨σ, hσ, h⟩ := hf
  obtain ⟨τ, hτ, h'⟩ := hg
  refine ⟨σ + τ, add_mem hσ hτ, fun k => ?_⟩
  simp only [map_add (f := _)]
  rw [h k, h' k, add_mul]

theorem extends_one (ht : t ∈ secs p L N) (e : ℕ) : Extends p L N D t 1 e := by
  refine ⟨t ^ e, ?_, fun k => ?_⟩
  · have hp := SetLike.pow_mem_graded e ht
    rwa [smul_eq_mul, mul_comm] at hp
  · rw [map_pow, map_pow, map_one]
    exact (_root_.one_mul _).symm

private theorem resG_constHom' {U V : X.Opens} (h : V ≤ U) (a : K) :
    resG X h (constHom p U a) = constHom p V a := by
  have hU : U ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e : p.appLE ⊤ U hU ≫ X.presheaf.map (homOfLE h).op = p.appLE ⊤ V (h.trans hU) := by
    rw [Scheme.Hom.appLE_map]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) e

theorem extends_const (a : K) : Extends p L N D t (constHom p D a) 0 := by
  refine ⟨fun j => constHom p (chart L j) a, ?_, fun k => ?_⟩
  · rw [mul_zero]
    intro i j
    rw [trans_zero, _root_.one_mul]
    change resG X _ (constHom p _ a) = resG X _ (constHom p _ a)
    rw [resG_constHom', resG_constHom']
  · rw [pow_zero, _root_.mul_one]
    change resG X _ (constHom p _ a) = resG X _ (constHom p _ a)
    rw [resG_constHom', resG_constHom']

private theorem extends_add (ht : t ∈ secs p L N) {f : Γ(X, D)} {e : ℕ}
    (hf : Extends p L N D t f e) (e' : ℕ) : Extends p L N D t f (e + e') := by
  simpa only [_root_.mul_one] using hf.mul (extends_one ht e')

theorem extends_eval₂ {J : Type} (ht : t ∈ secs p L N) (r : J → Γ(X, D))
    (hr : ∀ j, Extends p L N D t (r j) 1) (F : MvPolynomial J K) :
    ∃ e, Extends p L N D t (MvPolynomial.eval₂ (constHom p D) r F) e := by
  induction F using MvPolynomial.induction_on
  next a =>
    refine ⟨0, ?_⟩
    rw [MvPolynomial.eval₂_C]
    exact extends_const a
  next P Q hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    refine ⟨a + b, ?_⟩
    rw [MvPolynomial.eval₂_add]
    refine (extends_add ht ha b).add ?_
    rw [add_comm a b]
    exact extends_add ht hb a
  next P j hP =>
    obtain ⟨a, ha⟩ := hP
    refine ⟨a + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact ha.mul (hr j)

private theorem basicOpen_resG' {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    X.basicOpen (resG X h x) = V ⊓ X.basicOpen x :=
  Scheme.basicOpen_res X x (homOfLE h).op

theorem exists_locus (s : (lbPow L N).Sec) (f : Γ(X, Out.nonzeroLocus s)) (e : ℕ)
    (hf : Extends p L N (Out.nonzeroLocus s) (secEquiv p L N s : Fam p L) f e)
    (y : X) (hy : y ∈ X.basicOpen f) :
    ∃ (n : ℕ) (σ : (lbPow L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ X.basicOpen f := by
  obtain ⟨σ, hσ, h⟩ := hf
  have hmem : σ * (secEquiv p L N s : Fam p L) ∈ secs p L (N * e + N) :=
    SetLike.GradedMul.mul_mem hσ (secEquiv p L N s).2
  have key : ∀ k, (Out.nonzeroLocus s ⊓ chart L k) ⊓
      X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) =
      (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen f) ⊓
        (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen (evalFam p L k (secEquiv p L N s : Fam p L))) := by
    intro k
    rw [← basicOpen_resG' (inf_le_right : Out.nonzeroLocus s ⊓ chart L k ≤ _), map_mul, map_mul, h k,
      _root_.mul_assoc, ← pow_succ, Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ e.succ_pos,
      basicOpen_resG', basicOpen_resG']
  refine ⟨N * e + N, (secEquiv p L (N * e + N)).symm ⟨_, hmem⟩, ?_, ?_⟩
  · change y ∈ ⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))
    have hyD : y ∈ Out.nonzeroLocus s := X.basicOpen_le f hy
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (show y ∈ ⨆ k, X.basicOpen (s.f k) from hyD)
    have hkc : y ∈ chart L k := X.basicOpen_le _ hk
    have hmemk : y ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓
        X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) := by
      rw [key k]
      exact ⟨⟨⟨hyD, hkc⟩, hy⟩, ⟨⟨hyD, hkc⟩, hk⟩⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hmemk.2⟩
  · change (⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))) ≤ X.basicOpen f
    refine iSup_le fun k z hz => ?_
    have hz2 := hz
    rw [map_mul, Scheme.basicOpen_mul] at hz2
    have hz' : z ∈ X.basicOpen (s.f k) := hz2.2
    have hzD : z ∈ Out.nonzeroLocus s := TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hz'⟩
    have hkc : z ∈ chart L k := X.basicOpen_le _ hz'
    have hzk : z ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓
        X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) := ⟨⟨hzD, hkc⟩, hz⟩
    rw [key k] at hzk
    exact hzk.1.2

end GlobalTheory.AmpleBasis

namespace GlobalTheory

open SectionRing AmpleBasis

theorem exists_nonzeroLocus_le : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (O : P₀.A.left.Opens) (y : P₀.A.left), y ∈ O → ∃ (n : ℕ) (σ : (lbPow P₀.L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ O := by
  intro hL P₀ O y hy
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hL.ample ℂ P₀ 4 le_rfl
  have hyt : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
    rw [hcov]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hyt
  obtain ⟨haff, r, hr, hpoly⟩ := hs i
  obtain ⟨f, hfO, hyf⟩ := haff.exists_basicOpen_le ⟨y, hy⟩ hi
  obtain ⟨F, hF⟩ := hpoly f
  have hrj : ∀ j, Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i)) (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L)
      (r j) 1 := by
    intro j
    refine ⟨secEquiv P₀.A.hom P₀.L 4 (s j), ?_, fun k => ?_⟩
    · rw [Nat.mul_one]
      exact (secEquiv P₀.A.hom P₀.L 4 (s j)).2
    · rw [pow_one]
      exact hr j k
  obtain ⟨e, he⟩ := extends_eval₂ (secEquiv P₀.A.hom P₀.L 4 (s i)).2 r hrj F
  have he' : Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i))
      (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L) f e := by
    rw [hF]
    exact he
  obtain ⟨n, σ, hyσ, hσf⟩ := exists_locus (s i) f e he' y hyf
  exact ⟨n, σ, hyσ, hσf.trans hfO⟩

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.PushInv

open LBGerm

theorem exists_basisOn_any {S : Scheme.{0}} (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∃ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V), IsBasisOn P.A P.L V θ := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  haveI : IsOpenImmersion (snd T P.A).left := inferInstanceAs (IsOpenImmersion (pullback.snd T.hom P.A.hom))
  have hr : ∀ g : P.A.left, P.A.hom g ∈ V → g ∈ Set.range (snd T P.A).left := fun g hg => by
    rw [range_snd, hT]
    exact ⟨⟨_, hg⟩, rfl⟩
  choose θ hθ using fun i => exists_lift (snd T P.A).left (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) (fun g hg => hr g hg.1)
    ((LPow P.A P.L (1 : ℕ) T).U (fun _ => i)) (fun z hz => (mem_chart _ _ _ _ _ _).2 hz.2)
    ((b hq.default).f (fun _ => i))
  refine ⟨V, hV, θ, mem_secOn_of_germ θ fun g i j hg hi hj => ?_, fun R _ q hqV => ?_⟩
  · obtain ⟨z, rfl⟩ := hr g hg
    apply stalk_inj (snd T P.A).left z
    have hi' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => i)).2 hi
    have hj' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => j)).2 hj
    rw [map_mul, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) ⟨hg, hi⟩, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U j) ⟨hg, hj⟩,
      ← gm_comp _ (𝟙 _) z (P.L.U i ⊓ P.L.U j) ⟨hi, hj⟩, Category.comp_id]
    have e₁ := hθ i _ (𝟙 _) z ⟨hg, hi⟩
    have e₂ := hθ j _ (𝟙 _) z ⟨hg, hj⟩
    have e₃ := gm_lpow P.A P.L T (𝟙 _) z _ _ hi' hj'
    rw [Category.id_comp] at e₁ e₂ e₃
    rw [e₁, e₂, gs_compat (b hq.default) (𝟙 _) z hi' hj', e₃]
  · obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
      ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge), IsOpenImmersion.lift_fac _ _ _⟩
    choose b' hb' using fun i => exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
    obtain ⟨hli, hsp⟩ := hb R t b' hb'
    have e : (homAt t ▷ P.A).left ≫ (snd T P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    have val : ∀ (z : (baseAt t ⊗ P.A).left) i, (snd (baseAt t) P.A).left z ∈ P.L.U i →
        gs (𝟙 _) z _ ((b' hq.default).f (fun _ => i)) = gs (snd (baseAt t) P.A).left z _ (θ i) := fun z i hi => by
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have hV' : P.A.hom ((snd (baseAt t) P.A).left z) ∈ V := by
        rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]
        exact hqV ⟨_, rfl⟩
      have hm : (snd T P.A).left ((homAt t ▷ P.A).left z) ∈ P.A.hom ⁻¹ᵁ V ⊓ P.L.U i := by
        rw [← Scheme.Hom.comp_apply, e]; exact ⟨hV', hi⟩
      have e₁ := hθ i _ (homAt t ▷ P.A).left z hm
      rw [e] at e₁
      rw [e₁, hb' hq.default (fun _ => i)]
      exact (gs_appLE (homAt t ▷ P.A).left _ _ _ (𝟙 _) z hi' _).trans (by rw [Category.id_comp])
    refine ⟨fun s => ?_, fun r h0 => ?_⟩
    · rw [Set.range_unique] at hsp
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
      refine ⟨r, fun z i hi => ?_⟩
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have := gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hi'
      rw [hr] at this
      exact this.trans (congrArg _ (val z i hi))
    · refine Fintype.linearIndependent_iff.1 hli (fun _ => r) ?_ hq.default
      rw [Fintype.sum_unique]
      refine Subtype.ext (funext fun j => fn_ext fun z hz => ?_)
      obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
      have hi := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).1 hz
      refine (gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hz).trans ?_
      exact ((congrArg _ (val z i hi)).trans (h0 z i hi)).trans (gs_zero _ z _ hz).symm

theorem pushInvertible_any : Out.SecBaseChangeAnySt → Out.GlobalSectionsRankAlgClosed →
    ∀ (S : Scheme.{0}) (Q : Out.PolAV S), PushInvertible Q.A Q.L := by
  intro hS _ S P x
  obtain ⟨V, hV, θ, hθ, H⟩ := exists_basisOn_any hS P x
  haveI := P.smoothDim
  haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  refine ⟨V, hV, θ, hθ, fun W hW s hs => ?_, exists_nonvanishing H⟩
  have e : ∀ (a : Γ(S, W)) (g : P.A.left) i, P.A.hom g ∈ W → g ∈ P.L.U i →
      gs (𝟙 _) g _ ((P.A.hom.appLE W (P.A.hom ⁻¹ᵁ W ⊓ P.L.U i) inf_le_left).hom a *
        resG P.A.left (inf_le_inf_right _ (P.A.hom.preimage_mono hW)) (θ i)) =
      gs P.A.hom g W a * gs (𝟙 _) g _ (θ i) := fun a g i hg hi => by
    have hm : g ∈ P.A.hom ⁻¹ᵁ W ⊓ P.L.U i := ⟨hg, hi⟩
    rw [gs_mul (𝟙 _) g _ hm, gs_res (𝟙 _) g _ hm, gs_appLE _ _ _ _ (𝟙 _) g hm, Category.id_comp]
  obtain ⟨a, ha⟩ := exists_coeff H hW hs
  refine ⟨a, fun i => fn_ext fun g hg => (ha g i hg.1 hg.2).trans (e a g i hg.1 hg.2).symm, fun a' ha' => ?_⟩
  exact eq_of_mul H hW _ _ fun g i hg hi =>
    ((e a' g i hg hi).symm.trans (congrArg _ (ha' i).symm)).trans (ha g i hg hi)

end GlobalTheory.PushInv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegClause

theorem lbIso_pull_pull {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso L' (L.pull φ))
    (ψ : X'' ⟶ X') : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) (chartPullSame L _ _ _ ψ fun _ => rfl) h

theorem lbIso_lam_pull {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (e : A ⟶ B) [IsMonHom e] {L : LB A.left} {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull e.left)) : LBIso (abelian₂ A L) ((abelian₂ B M).pull (e ⊗ₘ e).left) := by
  have pa : ∀ I : Finset (Fin 2), psum A (x2 A) I ≫ e = (e ⊗ₘ e) ≫ psum B (x2 B) I := by
    intro I
    refine (psum_hom (MonoidHom.mk' (fun z : G2 A ⟶ A => z ≫ e) fun a b => MonObj.mul_comp a b _) _ I).trans
      (Eq.trans (congrArg (fun z => psum B z I) (funext fun k => ?_)) (psum_hom (preHom (e ⊗ₘ e)) _ I).symm)
    fin_cases k
    · exact (tensorHom_fst e e).symm
    · exact (tensorHom_snd e e).symm
  have hB : (abelian₂ B M).IsLB := DVR.linComb_isLB M hM _ _
  have r : LBIso (abelian₂ B M) (abelian₂ B M) := GlobalTheory.PolBaseChange.lbIso_refl hB
  have h₁ : LBIso (abelian₂ A L) (abelian₂ A (M.pull e.left)) := GlobalTheory.PowPrimitive.lbIso_linComb h _ _
  have h₂ : LBIso (abelian₂ A (M.pull e.left)) ((abelian₂ B M).pull (e ⊗ₘ e).left) :=
    LBIso.chartPull (chartPullLinComb M e.left (K := ULift.{0} (Finset (Fin 2)))
      (fun I => (psum A (x2 A) I.down).left) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) (e ⊗ₘ e).left (fun I => congrArg (fun z => z.left) (pa I.down)))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B M) _ _ rfl) r
  exact LBIso.trans (DVR.linComb_isLB L hL _ _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (pull_isLB hB _) h₁ h₂

end GlobalTheory.ZM.SiegClause
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.SquarePol

variable {S : Scheme.{0}}

def sqIsPowGrp (G : Over S) [GrpObj G] : Out.IsPowGrp (G ⊗ G) G 2 where
  pr := ![fst G G, snd G G]
  hom := fun i => by
    fin_cases i
    · exact inferInstanceAs (IsMonHom (fst G G))
    · exact inferInstanceAs (IsMonHom (snd G G))
  lim := Fan.IsLimit.mk _ (fun s => lift (s.proj 0) (s.proj 1))
    (fun s i => by
      fin_cases i
      · exact lift_fst _ _
      · exact lift_snd _ _)
    (fun s m hm => by
      apply CartesianMonoidalCategory.hom_ext
      · exact (hm 0).trans (lift_fst _ _).symm
      · exact (hm 1).trans (lift_snd _ _).symm)

def sqPol (P : Out.PolAV S) : Out.PolAV S :=
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI : ∀ i, IsMonHom ((sqIsPowGrp P.A).pr i) := (sqIsPowGrp P.A).hom
  { A := P.A ⊗ P.A
    isAb := (PowGrp.powers S _ P.A 2 (sqIsPowGrp P.A)).2.2.2.1 P.isAb
    g := 2 * P.g
    smoothDim := (PowGrp.powers S _ P.A 2 (sqIsPowGrp P.A)).2.2.1 P.g P.smoothDim
    L := Out.boxLB P.L (sqIsPowGrp P.A).pr
    isLB := DVR.linComb_isLB _ P.isLB _ _
    rigid := by
      obtain ⟨r, hr⟩ := P.rigid
      exact ⟨_, BoxPower.boxRig_isGen (sqIsPowGrp P.A) P.L r hr⟩
    sym := BoxPower.sym_box _ _ P.sym
    ample := relAmple_boxLB S _ P.A 2 (sqIsPowGrp P.A) P.L P.isLB P.ample
    ktriv := kTriv_boxLB S _ P.A 2 (sqIsPowGrp P.A) P.L P.isLB P.ktriv }

theorem sqPol_L (P : Out.PolAV S) :
    (sqPol P).L = LB.LinComb P.L (K := Fin 2) ![(fst P.A P.A).left, (snd P.A P.A).left] ![1, 1] := by
  simp only [sqPol, Out.boxLB]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem exists_square : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), ∃ (P₂ : Out.PolAV (Sp K)) (e : P₂.A ≅ P.A ⊗ P.A), IsMonHom (e.hom ≫ fst P.A P.A) ∧ IsMonHom (e.hom ≫ snd P.A P.A) ∧ P₂.g = 2 * P.g ∧ LBIso P₂.L (LB.LinComb P.L (K := Fin 2) ![(e.hom ≫ fst P.A P.A).left, (e.hom ≫ snd P.A P.A).left] ![1, 1]) := by
  intro K _ _ P
  refine ⟨sqPol P, Iso.refl _, ?_, ?_, rfl, ?_⟩
  · show IsMonHom (𝟙 (P.A ⊗ P.A) ≫ fst P.A P.A)
    rw [Category.id_comp]
    exact (sqIsPowGrp P.A).hom 0
  · show IsMonHom (𝟙 (P.A ⊗ P.A) ≫ snd P.A P.A)
    rw [Category.id_comp]
    exact (sqIsPowGrp P.A).hom 1
  · show LBIso (sqPol P).L (LB.LinComb P.L (K := Fin 2)
      ![(𝟙 (P.A ⊗ P.A) ≫ fst P.A P.A).left, (𝟙 (P.A ⊗ P.A) ≫ snd P.A P.A).left] ![1, 1])
    simp only [Category.id_comp]
    have h : LBIso (sqPol P).L (sqPol P).L := ⟨idIso _, idIso_isGen (sqPol P).isLB⟩
    rw [sqPol_L] at h ⊢
    exact h

end GlobalTheory.SquarePol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem relAmple_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.RelAmple (G i) (M i)) → Out.RelAmple A L := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hiso hA _ hamp
  have : IsProper A.hom := hA.proper
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S A L hL inferInstance inferInstance fun s => ?_
  obtain ⟨i, hi⟩ := exists_mem hU s
  obtain ⟨V, hV, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := U i) (x := s) hi
  have hle' : V ≤ U i := hle
  refine ⟨V, hs, ?_⟩
  have h := (hψ i).1
  have hf : S.homOfLE hle' ≫ (U i).ι = V.ι := S.homOfLE_ι hle'
  have sq : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = ((A.hom ∣_ V) ≫ S.homOfLE hle') ≫ (U i).ι := by
    rw [Category.assoc, hf, morphismRestrict_ι]
  let φ : (A.hom ⁻¹ᵁ V).toScheme ⟶ (G i).left := h.lift _ _ sq
  have hφ : φ ≫ ψ i = (A.hom ⁻¹ᵁ V).ι := h.lift_fst _ _ _
  have H : IsPullback φ (A.hom ∣_ V) (G i).hom (S.homOfLE hle') := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hφ, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  obtain ⟨w, hw⟩ : LBIso (L.pull (A.hom ⁻¹ᵁ V).ι) ((M i).pull φ) :=
    LBIso.chartPull (chartPullSame L (fun _ : PUnit => (A.hom ⁻¹ᵁ V).ι) (fun _ => ψ i) (fun _ => 1) φ fun _ => hφ.symm)
      (chartPullPull (M i) φ φ rfl) (hiso i).symm
  refine relAmple_pull (A' := Over.mk (A.hom ∣_ V)) H (hM i) (pull_isLB hL _) ((isGen_iff w).1 hw) ((U i).ι ⁻¹ᵁ V)
    (hV.preimage_of_isOpenImmersion _ (by simpa using hle')) (fun y => by
      have hy := congrArg (fun f : V.toScheme ⟶ S => f y) hf
      change ((S.homOfLE hle') y).val = y.val at hy
      change ((S.homOfLE hle') y).val ∈ V
      rw [hy]
      exact y.property) (hamp i)

end GlobalTheory.CoverGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.siegelPullback_id_comp_cancel : ∀ (h k : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (c'' : SiegPre h k ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), SiegPB c c (𝟙 _) ∧ (SiegPB c' c f → (SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f))) := by
  first | exact @GlobalTheory.SiegelPullComp.id_comp_cancel | exact GlobalTheory.SiegelPullComp.id_comp_cancel | (intros; apply GlobalTheory.SiegelPullComp.id_comp_cancel <;> assumption)
end
