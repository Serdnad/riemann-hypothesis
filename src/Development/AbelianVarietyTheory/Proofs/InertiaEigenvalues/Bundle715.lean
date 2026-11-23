module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle644
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle675
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle615
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle532
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle429
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle395
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle672
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle492
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SideLevel
open Formalism.IndefR.Lev

theorem surj_restrict {A G : Type} [Group A] [Group G] {J Q Q' : Subgroup A} (h : Q' ≤ Q) (red : Q →* G)
    (hs : Function.Surjective red) (hk : ∀ q : Q, red q = 1 ↔ (q : A) ∈ J)
    (hm : ∀ g ∈ Q, ∃ g' ∈ Q', g⁻¹ * g' ∈ J) : Function.Surjective (red.comp (Subgroup.inclusion h)) := by
  intro g
  obtain ⟨q, rfl⟩ := hs g
  obtain ⟨g', hg', hJ⟩ := hm q q.2
  refine ⟨⟨g', hg'⟩, ?_⟩
  have h1 : red (q⁻¹ * ⟨g', h hg'⟩) = 1 := (hk _).2 hJ
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm



theorem sideReal_moreLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok ok' : Set Pl0) (Sp : Set (Pl D.host.E)), L.Q ⊆ Q' → ok' ⊆ ok → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → (∀ P ∈ ok', Bridge.SplitOff (pl P) Sp) → (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ∈ Sp) → (∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ)) → (∀ PP ∈ Q', ∀ x, ∃ a, D.what₂.embLL a = ((xq PP x : ℂˣ) : ℂ)) → ∀ (c : Bridge.CoefDat D V) (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : ok × ℕ → Module.End D.what₂.LL S.Forms) (B : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β L pl ok)) S act op (fun i => i.2)), (∃ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (rho : _) (pair : _) (nab del : _), Bridge.CoefMapTie V c c0 rho ∧ Bridge.CoefTie V c B.pres lam c0 pair nab del) → ∃ (S' : CSD D.what₂.LL) (act' : Representation D.what₂.LL G S'.Forms) (op' : ok' × ℕ → Module.End D.what₂.LL S'.Forms) (B' : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β { L with Q := Q', xq := xq } pl ok')) S' act' op' (fun i => i.2)), (∀ q : (levEnv V β { L with Q := Q', xq := xq }).Q, ∃ hq : (q : Bridge.Gf V) ∈ (levEnv V β L).Q, B'.act_tie.red q = B.act_tie.red ⟨q, hq⟩) ∧ (∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair nab del, Bridge.CoefTie V c B.pres lam c0 pair nab del → Bridge.CoefTie V c B'.pres lam c0 pair nab del) ∧ ∀ P, op' (P, 0) = 1 ∧ ∀ k, V.rank < k → op' (P, k) = 0 := by
  intro D G _ _ V β Λ hSD L Q' xq Pl0 pl ok ok' Sp hQ hok hdisj hsplit hS hcg hxq c S act op B hct
  have hfin := GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ
  obtain ⟨hJle, hQle, hfi, hker⟩ := hfin
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  have hSD' : IsSDFrame V β Λ 1 := ⟨cc, by rw [one_pow]; exact hβ⟩
  let L' : LevDat D.host.E ℂ V.rank := { L with Q := Q', xq := xq }
  have hval : ∀ q : (levEnv V β L').Q, ∃ a, D.what₂.embLL a = (((levEnv V β L').ch q : ℂˣ) : ℂ) :=
    fun q => GlobalTheory.TwistCharChange.flag_vals V β L' hcg hxq _
  have hvalJ : ∀ k : (levEnv V β L').J, ∃ a, D.what₂.embLL a = (((levEnv V β L').χ k : ℂˣ) : ℂ) := by
    intro k
    rw [← (levEnv V β L').ch_J k]
    exact hval _
  have hrat : ∀ (γ : GQ V) x, ∃ x', B.pres.coef x' = c.ρ γ (B.pres.coef x) := by
    obtain ⟨lam, c0, rho, pair, nab, del, hmap, e, -, hco, -⟩ := hct
    intro γ x
    obtain ⟨γE, hγ⟩ := GlobalTheory.TwistCharChange.ratMat_exists V γ
    refine ⟨e.symm (rho γE (e x)), ?_⟩
    refine ((hco _).trans ?_).trans (congrArg (c.ρ γ) (hco x)).symm
    rw [LinearEquiv.apply_symm_apply]
    exact hmap.1 γ γE hγ (e x)
  obtain ⟨Cl, fC, π, kc, Gam, gG, fG, ρ', P', hy, hcoef⟩ := GlobalTheory.T.classPres_of_finiteIndex_subLevel (Bridge.ratF V) D.what₂.embLL S c.ρ
    (levEnv V β L).J (levEnv V β L).χ B.pres (levEnv V β L').J hJle hfi (levEnv V β L').χ hvalJ hrat
  have hrat' : ∀ (γ : GQ V) x, ∃ x', P'.coef x' = c.ρ γ (P'.coef x) := by
    rw [hcoef]; exact hrat

  let red' : (levEnv V β L').Q →* G := B.act_tie.red.comp (Subgroup.inclusion hQle)
  have hred_surj : Function.Surjective red' :=
    surj_restrict hQle B.act_tie.red B.act_tie.red_surj B.act_tie.red_ker (GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks D V β Λ hSD' L Q' xq hQ hdisj)
  have hred_ker : ∀ q : (levEnv V β L').Q, red' q = 1 ↔ (q : Bridge.Gf V) ∈ (levEnv V β L').J := by
    intro q
    exact (B.act_tie.red_ker ⟨q, hQle q.2⟩).trans ⟨fun h => hker _ q.2 h, fun h => hJle h⟩

  let up : ok' × ℕ → ok × ℕ := fun i => (⟨i.1, hok i.1.2⟩, i.2)
  have hoffI : ∀ i : ok' × ℕ, ∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1) :=
    fun i PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff (hsplit i.1.1 i.1.2) PP (hS PP h)
  have hHk : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → isTEnv V pl ok' i (B.hecke.hx (up i)) ∧
      (∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok' i a) ∧ Bridge.IsDC (levEnv V β L').J (B.hecke.hx (up i)) (B.hecke.hA (up i)) := by
    intro i hi
    have hT : isTEnv V pl ok (up i) (B.hecke.hx (up i)) := B.hecke.hx_ok (up i) hi
    have hA : ∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok (up i) a := B.hecke.hA_loc (up i) hi
    refine ⟨hT, hA, ?_⟩
    exact GlobalTheory.T.hecke_representatives_split_place_smaller_level D V β Λ hSD' L Q' xq hQ Pl0 pl ok (up i) (hoffI i) hi.2 _ _ hT hA (B.hecke.hDC (up i) hi)
  have hloc : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → ∃ Lc : Subgroup (Bridge.Gf V),
      (∀ x, isLocEnv V pl ok' i x → x ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L').J, ∃ k₁ ∈ (levEnv V β L').J, ∃ k₂ ∈ (levEnv V β L').J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧
        ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : (levEnv V β L').J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L').χ k = 1 := by
    intro i hi
    obtain ⟨α, hα, -⟩ := B.hecke.hx_ok (up i) hi hi.2
    obtain ⟨e, -, he, -⟩ := hα
    obtain ⟨Lc, l1, l2, l3, -⟩ := GlobalTheory.SplitHeckeAdj.local_group V β Λ L' hβ (pl i.1) e he (hoffI i)
    refine ⟨Lc, fun x hx => ?_, l2, l3⟩
    obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp V hx he
    exact l1 g hg
  obtain ⟨act', op', B', hpres, hred, hop⟩ := GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators (Bridge.ratF V) c (levEnv V β L') (isTEnv V pl ok')
    (isLocEnv V pl ok') D.what₂.embLL _ (fun i : ok' × ℕ => 1 ≤ i.2 ∧ i.2 ≤ V.rank) P' hval hrat' red' hred_surj hred_ker
    (fun i => B.hecke.hx (up i)) (fun i => B.hecke.hA (up i)) hHk hloc (fun i => i.2 = 0)
  subst hpres
  have hl : ∀ cl, Bridge.hLat V (B'.pres.y cl) = Bridge.hLat V (B.pres.y (π cl)) := fun cl =>
    (congrArg (Bridge.hLat V) (hy cl)).trans (GlobalTheory.T.hermitian_lattice_invariant_under_level D V β Λ hSD' L _ _ (kc cl).2)
  refine ⟨_, act', op', B', fun q => ⟨hQle q.2, DFunLike.congr_fun hred q⟩, ?_, ?_⟩
  · rintro lam c0 pair nab del ⟨e, h1, h2, h3, h4, h5⟩
    exact ⟨e, h1, fun x => (DFunLike.congr_fun hcoef x).trans (h2 x), h3,
      fun cl => (h4 (π cl)).trans (congrArg nab (hl cl).symm), fun cl => (h5 (π cl)).trans (congrArg del (hl cl).symm)⟩
  · intro P
    refine ⟨(hop (P, 0) (by simp)).1 rfl, fun k hk => (hop (P, k) (by simp only [not_and, not_le]; intro; omega)).2 (by simp only; omega)⟩

end GlobalTheory.SideLevel
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem dcris_exact_strict_elementwise : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  intro D l _ K LL
  have hA := (GlobalTheory.T.ramifiedCoefficientChains_adm11 D l K LL).1
  intro hbij V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ _ _ _ _ _ _ hιe hπe hinj hsurj
    hker c₀ c₁ c₂
  obtain ⟨h1, h2, h3, h4⟩ :=
    hA hbij V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π hιe hπe hinj hsurj hker.symm c₀ c₁ c₂
  refine ⟨h1, ?_, h3, fun a => (h4 a).1, ?_⟩
  · intro x hx hπx
    exact Submodule.mem_map.mp (h2.ge ⟨hx, hπx⟩)
  · intro a y hy hyF
    exact (h4 a).2.ge ⟨hy, hyF⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc

theorem finiteDimensional_Ks_one {l : ℕ} [Fact l.Prime] (K : FinExt l) (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    FiniteDimensional ℚ_[l] ↥(Ks K 1) := by
  have h0 : K0 K = K.1 := inf_eq_left.mpr hK
  have hK1 : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin : ({x : Om l | x ^ (l ^ 1) = 1}).Finite := by
    apply ((Polynomial.nthRoots (l ^ 1) (1 : Om l)).toFinset.finite_toSet).subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (pow_pos hl 1)).2 hx
  haveI : Finite ({x : Om l | x ^ (l ^ 1) = 1}) := hfin.to_subtype
  have hA : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}) := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    refine ⟨Polynomial.X ^ (l ^ 1) - 1, Polynomial.monic_X_pow_sub_C 1 (pow_pos hl 1).ne', ?_⟩
    simp only [Set.mem_setOf_eq] at hx
    simp only [pow_one] at hx
    simp [hx]
  unfold Ks
  rw [h0]
  infer_instance

theorem exists_caseA_enl : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q →
    D.nd.l i ≠ D.host.d → ∃ C : TruncatedSeriesCountingIdentities.CoefExt D i w hw, CaseA (D.nbr i w hw).Kw C.LL := by
  intro D i w hw hs hq hd
  have h2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hs
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.HubLoc.kw_le_Kur_all D i hs hq hd w hw
  haveI := finiteDimensional_Ks_one (D.nbr i w hw).Kw hur
  haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).LL.1 := (D.nbr i w hw).LL.2
  let N : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    IntermediateField.normalClosure ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1) (Om (D.nd.l i))
  haveI hN : FiniteDimensional ℚ_[D.nd.l i] ↥N := normalClosure.is_finiteDimensional _ _ _
  let LL : FinExt (D.nd.l i) := ⟨N ⊔ (D.nbr i w hw).LL.1, inferInstance⟩
  refine ⟨⟨LL, le_sup_right⟩, hur, h2, le_rfl, fun h => absurd h h2, ?_, ?_⟩
  · have h0 : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hur
    unfold Ks
    rw [h0]
    exact le_sup_left
  · intro τ x
    apply le_sup_left (b := (D.nbr i w hw).LL.1)
    exact AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩

end GlobalTheory.UseLoc
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardFrobeniusPower

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem isUnit_φA_pow (k : ℕ) (a : LetA O n) (ha : IsUnit (algebraMap (LetA O n) W.EE a)) :
    IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) a)) := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply]
    have : algebraMap (LetA O n) W.EE (W.φA ((W.φA ^ k) a)) =
        W.φE (algebraMap (LetA O n) W.EE ((W.φA ^ k) a)) := (W.φE_ext _).symm
    rw [this]
    exact ih.map W.φE

theorem isUnit_X : IsUnit (algebraMap (LetA O n) W.EE W.X) :=
  isUnit_φA_pow W (W.s - 1) letπ W.EE_π

theorem Q_pow_φ_mem [NeZero n] (T : LocLat G Qp LL O) (M : ZMod n → ℕ)
    (hM : ∀ i, ∀ x ∈ W.Nl T (i - 1), W.Q ^ (M i) • W.φD T x ∈ W.N T)
    (x : W.DD T) (hx : x ∈ W.N T) : W.Q ^ (mx M) • W.φD T x ∈ W.N T := by
  have hx' : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE, one_smul]

  rw [hx', map_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hle : M (i + 1) ≤ mx M := le_ciSup (Set.finite_range M).bddAbove (i + 1)
  have hmem : (letE i : LetA O n) • x ∈ W.Nl T (i + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨x, hx, by simp⟩
  have h1 := hM (i + 1) _ hmem
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ h1

theorem core [NeZero n] (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (M : ZMod n → ℕ)
    (hex : ∀ y, W.map π y = 0 → ∃ z, W.map ι z = y)
    (hsat : ∀ z : W.DD T, W.map ι z ∈ W.N Tp → z ∈ W.N T)
    (hφ : ∀ i, ∀ x ∈ W.Nl Tp (i - 1), W.Q ^ (M i) • W.φD Tp x ∈ W.N Tp)
    (hγ : ∀ x ∈ W.N Tp, W.γ Tp x - x ∈ (aN W) Tp W.X)
    (e : W.DD W.one) (he : W.φD W.one e = e) (hge : ∀ g, W.γD W.one g e = e)
    (x : W.DD Tp) (hx : x ∈ W.N Tp) (c : O) (hc : W.map π x = c • e) :
    (∃ y ∈ (invN W) T (W.Q ^ mx M), W.map ι y = W.φD Tp x - x) ∧
      (∃ z ∈ (aN W) T W.X, W.map ι z = W.γ Tp x - x) := by
  constructor
  · have h0 : W.map π (W.φD Tp x - x) = 0 := by
      rw [map_sub, W.map_φ, hc, (W.φD W.one).map_smul, he, sub_self]
    obtain ⟨y, hy⟩ := hex _ h0
    refine ⟨y, hsat _ ?_, hy⟩
    change W.map ι (W.Q ^ mx M • y) ∈ W.N Tp
    rw [map_smulA, hy, smul_sub]
    exact Submodule.sub_mem _ (Q_pow_φ_mem W Tp M hφ x hx) (Submodule.smul_mem _ _ hx)
  · obtain ⟨w, hw, hw'⟩ := hγ x hx
    change W.X • w = W.γ Tp x - x at hw'
    have hX0 : W.X • W.map π w = 0 := by
      rw [← map_smulA, hw', map_sub, LocWach.γ, W.map_γ, hc, (W.γD W.one W.gam).map_smul, hge,
        sub_self]
    have h0 : W.map π w = 0 := by
      obtain ⟨u, hu⟩ := isUnit_X W
      rw [← algebraMap_smul W.EE W.X, ← hu] at hX0
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hX0
      simpa [smul_smul] using this
    obtain ⟨z, hz⟩ := hex _ h0
    have hzN : z ∈ W.N T := hsat z (hz ▸ hw)
    refine ⟨W.X • z, ⟨z, hzN, rfl⟩, ?_⟩
    rw [map_smulA, hz]
    exact hw'

end Generic



theorem crystalline_extension_integral_cocycle_all_places : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P8 D HW F := by
  intro D HW F Cm l _ K s LL h T M hh hT hjT Tp ι π hses hTp e heN hφe hγe x hx c hc
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hexact : Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) := by
    let E := ((F l).E K s LL h).tie
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
    exact (GlobalTheory.EtaleExact.exact_of_tie E
      (GlobalTheory.EtaleExact.map_ne_top_of_tie E (by
        rw [hp]
        exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL) (by
        rw [hp]
        exact GlobalTheory.EtaleExact.sep_RW LL)) T Tp ((HW l).W K s LL h).one ι π hses).2.1
  have hsat := GlobalTheory.T.mem_wachN_of_map_mem_saturated D HW F l K s LL h T Tp ((HW l).W K s LL h).one ι π hT hTp
    (GlobalTheory.NL.one_crys (HW l) h) hses
  have hjs := GlobalTheory.NL.JumpsSES.jumps_ses_and_one D HW l K s LL h T Tp ((HW l).W K s LL h).one ι π hTp hses
  have hjTp : JumpsLet ((HW l).W K s LL h) Tp M hh := by
    intro τ i hτ a ha
    rcases (hjs.1 τ a).1 ha with h1 | h1
    · exact hjT τ i hτ a h1
    · rw [hjs.2 τ a h1]
      exact ⟨by simp, by simp⟩
  have h5 := (GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm l K s LL h Tp M hh hTp hjTp).1
  have h2 := (GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm l K s LL h Tp hTp).2.2
  exact core _ T Tp ι π M (fun y hy => (hexact y).1 hy) hsat h5 h2 e hφe hγe x hx c hc

end GlobalTheory.NL.NygaardFrobeniusPower
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.IntComplex



theorem ring_part (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) :
    let W := (HW l).W K s LL h
    (∃ w, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X}) ∧ ∃ b, W.X = letπ * b := by
  intro W
  obtain ⟨χ, -, -, hγ, hX, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  have hs : 1 ≤ s := h.1
  obtain ⟨-, -, -, -, -, hact, -⟩ := GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s hs
  obtain ⟨-, b, hb⟩ := hact (χ W.gam)
  refine ⟨⟨1 + W.X * fun _ => b, ?_, ?_⟩, ?_⟩
  · funext i
    change W.γ₀ W.gam (W.Q i) = (1 + W.X i * b) * W.Q i
    rw [hγ, hX, hQ, hb, mul_comm]
  · rw [add_sub_cancel_left]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  · obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries ↥(OL LL)) ∣ GlobalTheory.Cyc.XX l ↥(OL LL) s := by
      rw [PowerSeries.X_dvd_iff, GlobalTheory.Cyc.XX]
      simp
    refine ⟨fun _ => c, ?_⟩
    funext i
    change W.X i = PowerSeries.X * c
    rw [hX, hc]



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2c D HW F := by
  intro D HW F l _ K s LL h T M hh hT _
  obtain ⟨h1, b, hb⟩ := ring_part D HW l K s LL h
  refine ⟨h1, fun y z hy hz hc => ?_⟩
  have hz' : z ∈ aN ((HW l).W K s LL h) T letπ := by
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨b • x, Submodule.smul_mem _ b hx, ?_⟩
    simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hb, mul_smul]
  refine ⟨?_, fun h0 => ?_⟩
  · refine GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F l K s LL h T hT (Multiset.replicate (mx M) 0) y z ?_ hz' hc
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_zero]
    exact hy
  · obtain ⟨m, hm⟩ := ((GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F l K s LL h T hT).1.2 ⟨(y, z), hc⟩).1 h0
    have hm1 : y = ((HW l).W K s LL h).φD T m - m := congrArg Prod.fst hm
    have hm2 : z = ((HW l).W K s LL h).γ T m - m := congrArg Prod.snd hm
    refine ⟨m, GlobalTheory.T.mem_wach_of_frobenius_gamma D HW F l K s LL h T hT (mx M) m ?_ ?_, hm1, hm2⟩
    · exact hm1 ▸ hy
    · exact hm2 ▸ hz'

end GlobalTheory.NL.IntComplex
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaEigenvalues.DimAtQD

theorem main : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc),
    EmbeddingTypeJumps.AtQD i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Formalism.WeaklyAdmissibleFiltrations.BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 :=
  fun _ _ D i _ w hw C =>
    by
      classical
      haveI := (D.nbr i w hw).Kw.2
      haveI := C.LL.2
      exact @GlobalTheory.BlochKatoTied.blochKatoDim_of_tied (D.nd.l i) _ (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.nbr i w hw).Kw C.LL _

end GlobalTheory.InertiaEigenvalues.DimAtQD
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.bloch_kato_right_exact : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.bkARightExact (P.PD K) := by
  first | exact @GlobalTheory.BKRightExact.bkARightExact_of_tied | exact GlobalTheory.BKRightExact.bkARightExact_of_tied | (intros; apply GlobalTheory.BKRightExact.bkARightExact_of_tied <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoLocalOfHyp

theorem bkAll_of_blochKatoLocal (hBK : GlobalTheory.Published.BlochKatoLocal) (hTD : Formalism.GaloisCohomology.LocalTateDualityK)
    (hEC : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.bkAll (P.PD K) := by
  obtain ⟨hDim, hRat, hInt⟩ := hBK l P AI hT K
  have hA : bkACore (P.PD K) := GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality l P K hRat
  have hB : bkBCore (P.PD K) := GlobalTheory.T.blochKato_annihilator_of_integralLocalDuality l P K hInt
  exact ⟨hA, GlobalTheory.T.blochKatoDim_of_Ql_dimensionFormula l P K hDim, GlobalTheory.BKRightExact.bkARightExact_of_tied l P AI hT K, hB,
    GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level hTD hEC l P AI hT K hA hB⟩

theorem blochKatoLocal_allPrimes_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.LocalSituation.Conclusion5 D := by
  intro hBK hTD hEC D l _ K
  exact bkAll_of_blochKatoLocal hBK hTD hEC l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.BlochKatoLocalOfHyp
end
