module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import GroundTheory.LocalFields.PadicLogSeries
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle131
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

open GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem finPart_mem_integral_iff (k : finU (E := E) (n := a)) :
    finPart E a k ∈ AdelicGLn.integralFiniteGL E a ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isOpen_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E))) := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  have h : IsOpen (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) : Set (GL (Fin a) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isOpen_KO
  rwa [hK] at h

theorem isClosed_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsClosed (GlobalTheory.LFun.KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E))) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_KGL w a)

theorem mem_intU_iff_of_mem_locU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) :
    x ∈ intU a w ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) :=
  ⟨fun h => (mem_intU.1 h).2 w (fun h' => h' rfl), mem_intU_of hx⟩

theorem isOpen_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
  have e : (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) =
      (fun x : locU a w => cLoc w x.1) ⁻¹' (GlobalTheory.LFun.KGL w (n := a) : Set _) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    exact mem_intU_iff_of_mem_locU x.2
  rw [e]
  exact (isOpen_KGL w a).preimage ((continuous_cLoc w).comp continuous_subtype_val)

theorem isCompact_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact (intU a w : Set (UA E a)) := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) :=
    fun _ => Units.isEmbedding_embedProduct.t2Space
  let T : Set (finU (E := E) (n := a)) := {x | x.1 ∈ intU a w}
  have hK0 : IsCompact {x : finU (E := E) (n := a) | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} :=
    isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad)
  have hTsub : T ⊆ {x : finU (E := E) (n := a) | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} := by
    intro x hx
    have hx' := mem_intU.1 hx
    have hall : ∀ u, cLoc u x.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
      intro u
      by_cases hu : Apart u w
      · rw [((GlobalTheory.Cong.LevelExt.mem_locU_iff x.1).1 hx'.1).2 u hu]
        exact one_mem _
      · exact hx'.2 u hu
    refine ⟨finPart E a x, (finPart_mem_integral_iff x).2 hall, ?_⟩
    have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  have hTe : T = (⋂ u, ⋂ (_ : Apart u w), {x : finU (E := E) (n := a) | cLoc u x.1 = 1}) ∩
      ⋂ u, ⋂ (_ : ¬ Apart u w), {x : finU (E := E) (n := a) | cLoc u x.1 ∈ GlobalTheory.LFun.KGL u (n := a)} := by
    ext x
    simp only [T, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mem_intU,
      GlobalTheory.Cong.LevelExt.mem_locU_iff]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨x.2, h.1⟩, h.2⟩⟩
  have hTc : IsClosed T := by
    rw [hTe]
    refine (isClosed_iInter fun u => isClosed_iInter fun _ => ?_).inter
      (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
    · exact (isClosed_KGL u a).preimage ((continuous_cLoc u).comp continuous_subtype_val)
  have hT := (hK0.of_isClosed_subset hTc hTsub).image continuous_subtype_val
  have e : Subtype.val '' T = (intU a w : Set (UA E a)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      exact ⟨⟨y, ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 (intU_le_locU w hy)).1⟩, hy, rfl⟩
  rwa [e] at hT

theorem intU_isCompact_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsCompact (GlobalTheory.Cong.AdaptLev.intU a w : Set (UA E a)) ∧ IsOpen (((GlobalTheory.Cong.AdaptLev.intU a w).subgroupOf (locU a w)) : Set (locU a w)) :=
  fun _ _ _ _ _ w => ⟨isCompact_intU w, isOpen_intU w⟩

end GlobalTheory.Cong.AdaptLev
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU (E := E) (n := a)) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact (MonoidHom.mem_ker.1 hx).trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij] <;> rfl

theorem mem_integral_iff (k : finU (E := E) (n := a)) :
    k ∈ (AdelicGLn.integralFiniteGL E a).comap (finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isCompact_integral :
    IsCompact (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) := by
  have hO : IsOpen (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) :=
    (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.Cong.AutFormFix

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

theorem fixed_intU_eventually : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ),
    IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  intro E _ _ _ a φ hφ
  classical
  set St : Set (finU (E := E) (n := a)) := {k : finU (E := E) (n := a) | RU E a k φ = φ} with hSt
  set K₀ : Set (finU (E := E) (n := a)) := (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a)))
  let t : Finset (HeightOneSpectrum (𝓞 E)) → Set (finU (E := E) (n := a)) := fun S =>
    {k : finU (E := E) (n := a) | ∀ u ∈ S, cLoc u k.1 = 1} ∩ Stᶜ
  have htc : ∀ S, IsClosed (t S) := by
    intro S
    refine IsClosed.inter ?_ hφ.level.isClosed_compl
    have : {k : finU (E := E) (n := a) | ∀ u ∈ S, cLoc u k.1 = 1} = ⋂ u ∈ S, {k : finU (E := E) (n := a) | cLoc u k.1 = 1} := by
      ext k; simp
    rw [this]
    refine isClosed_biInter fun u _ => ?_
    haveI : T2Space (GL (Fin a) (u.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
  have hst : K₀ ∩ ⋂ S, t S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun k hk => ?_
    have hall : ∀ u, cLoc u k.1 = 1 := fun u =>
      (Set.mem_iInter.1 hk.2 {u}).1 u (Finset.mem_singleton_self u)
    have h1 : k = 1 := Subtype.ext (eq_one_of_forall_cLoc k.2 hall)
    have hnot := (Set.mem_iInter.1 hk.2 ∅).2
    apply hnot
    rw [h1]
    show RU E a ((1 : finU (E := E) (n := a)) : UA E a) φ = φ
    rw [Subgroup.coe_one, map_one]; rfl
  have hdt : Directed (· ⊇ ·) t := by
    intro S₁ S₂
    refine ⟨S₁ ∪ S₂, ?_, ?_⟩ <;> rintro k ⟨hk, hk'⟩ <;> refine ⟨fun u hu => hk u ?_, hk'⟩ <;> simp [hu]
  obtain ⟨S, hS⟩ := isCompact_integral.elim_directed_family_closed t htc (Set.disjoint_iff_inter_eq_empty.mpr hst) hdt
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ u ∈ S, Apart u w}.Finite := by
    refine ((S.finite_toSet.biUnion fun u _ => (Set.toFinite ({u, conjSrc (GlobalTheory.SplitPts.conjE E) u} : Set _)))).subset ?_
    intro w hw
    simp only [Set.mem_setOf_eq, not_forall, Apart, not_not] at hw
    obtain ⟨u, hu, he⟩ := hw
    refine Set.mem_biUnion hu ?_
    rcases eq_or_eq_conjSrc he.symm with rfl | rfl
    · simp
    · simp
  refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hS'
  apply hw
  intro x hx
  obtain ⟨hxl, hxi⟩ := GlobalTheory.Cong.AdaptLev.mem_intU.1 hx
  have hxf : x ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hxl).1
  have hcomp : ∀ u, Apart u w → cLoc u x = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hxl).2 u) hu)
  have hK : (⟨x, hxf⟩ : finU (E := E) (n := a)) ∈ K₀ := by
    refine (mem_integral_iff _).2 fun u => ?_
    by_cases hu : Apart u w
    · show cLoc u x ∈ _
      rw [hcomp u hu]; exact one_mem _
    · exact hxi u hu
  by_contra hne
  have : (⟨x, hxf⟩ : finU (E := E) (n := a)) ∈ K₀ ∩ t S := ⟨hK, fun u hu => hcomp u (hS' u hu), hne⟩
  exact (Set.disjoint_left.mp hS) this.1 this.2

end GlobalTheory.Cong.AutFormFix
end
end

section

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem vAdd_mul_of_ne {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add]

theorem vAdd_pow_eq (x : K) (n : ℕ) : vAdd w (x ^ n) = n * vAdd w x := by
  unfold vAdd
  rw [map_pow, WithZero.log_pow]
  simp

theorem vAdd_prod_of_ne {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i, f i ≠ 0) :
    vAdd w (∏ i ∈ s, f i) = ∑ i ∈ s, vAdd w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vAdd]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, vAdd_mul_of_ne w (h a) (Finset.prod_ne_zero_iff.2 fun i _ => h i), ih]

theorem vAdd_nonneg_of_le {x : K} (hx : x ≠ 0) (h : w.valuation K x ≤ 1) : 0 ≤ vAdd w x := by
  unfold vAdd
  have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hx) one_ne_zero).2 h
  rw [WithZero.log_one] at this
  omega

theorem mem_of_vAdd_pos {a : 𝓞 K} (h : 0 < vAdd w (a : K)) : a ∈ w.asIdeal := by
  by_contra hn
  have h1 : w.valuation K (a : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 hn
  rw [vAdd, h1, WithZero.log_one] at h
  omega

end Val

theorem sum_nuW_nonneg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {j : ℕ} (hj : j < R.m)
    (τ : X.Tau) : 0 ≤ ∑ a, (W.nuW u (j + 1) τ).w a := by
  obtain ⟨s, s', ⟨h1, h2, -⟩, h3⟩ := chainWeights X Pr R W u j hj
  refine Finset.sum_nonneg fun a _ => ?_
  have h4 := (W.lamTrue u (j + 1) τ).anti (show Fin.castLE (N_lt_succ R j).le a ≤ ⟨R.N j, N_lt_succ R j⟩ from a.2.le)
  rw [h2 τ _ le_rfl] at h4
  rw [← h3, ← h1]
  omega

theorem recWts_ok {D : D7} (EX : ErrX D) : (recWts EX).Ok := by
  exact
    { row_ok τ := ⟨D.hc τ, rfl⟩
      hc_row := recWts_row EX
      u_first u u' τ h := (D.hcW_first u τ h).trans (D.hcW_first u' τ h).symm
      u_last u u' τ h := (D.hcW_last u τ (by omega)).trans (D.hcW_last u' τ (by omega)).symm }

theorem emb_star_piG {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    (recFields D).emb τ (@star _ (recFields D).starE.toStar (((recPrimes EX).piG i : 𝓞 D.host.E) : D.host.E)) = tauPib EX i τ := by
  have h : ∀ x : D.host.E, @star _ (recFields D).starE.toStar x = D.host.conj x := fun x => by
    apply D.host.φ₀.injective
    let _ := D.host.isCMField_hostE
    change D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  rw [h]
  rfl

theorem vG_loss_le {D : D7} (L : SizeData₂ D) (EX : ErrX D) (hPr : (recPrimes EX).Ok) (i : Fin 2) (w : LiftErrorLocal.Pl D)
    (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) :
    (∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0) ∧
    LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) ≤
      (∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) + LiftErrorLocal.errC D L := by
  have hg0 : (D.host.g i : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hπ : ∀ τ, tauPib EX i τ ≠ 0 := by
    intro τ h
    have h1 : (recFields D).emb τ (((recFields D).conjO (EX.piG i) : 𝓞 D.host.E) : D.host.E) = 0 :=
      (emb_star_piG EX i τ).trans h
    have h2 : (recFields D).conjO (EX.piG i) = 0 := RingOfIntegers.ext ((map_eq_zero _).1 h1)
    have h3 := hPr.piG_norm i
    change EX.piG i * (recFields D).conjO (EX.piG i) = _ at h3
    rw [h2, mul_zero] at h3
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h3.symm)
  have e : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j = (D.host.g i : D.what₂.LL) ^ (D.R.f * D.R.N j * D.R.N (j + 1)) *
      ∏ τ, tauPib EX i τ ^ (∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat := fun j => by
    rw [← D.what₂.card_Tau]
    simp only [← emb_star_piG]
    rfl
  have hne : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0 := fun j => by
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ))
  refine ⟨hne, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hvg : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ hg0] at h1
    exact_mod_cast h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h1 : ∀ j ∈ Finset.range D.R.m, (vAdd (D.plEq w) (lossAt (Pr := recPrimes EX) (recWts EX) i u j) : ℝ) / D.what₂.places.ramIdx w ≤
      vNN EX i u (1 + j) w + D.R.f * (D.R.N D.R.m * (D.R.N D.R.m + D.R.t)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h2 : (D.R.f : ℝ) * D.R.N j * D.R.N (j + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
      exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.exp_le D j hj'
    have h3 : ∀ τ, (((∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat : ℕ) : ℝ) = nuAbs D u (1 + j) τ := fun τ => by
      rw [add_comm 1 j, partitionSize D EX u j hj' τ, ← Int.cast_natCast,
        Int.toNat_of_nonneg (sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj' τ)]
    rw [e, vAdd_mul_of_ne _ (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ)),
      vAdd_prod_of_ne _ _ _ fun τ => pow_ne_zero _ (hπ τ)]
    simp only [vAdd_pow_eq, hvg]
    push_cast
    simp only [h3]
    rw [add_div, mul_div_assoc, div_self he.ne', mul_one, vNN]
    linarith
  have h4 : 0 ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) ^ 3 * L.etaSz) := by
    have := L.etaSz_pos.le
    positivity
  unfold LiftErrorLocal.vG
  rw [vAdd_prod_of_ne _ _ _ hne, Int.cast_sum, Finset.sum_div]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, LiftErrorLocal.lifts, LiftErrorLocal.errC,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  nlinarith

end GlobalTheory.ColPeriod
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong

theorem locU_conj_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (y : UA E a) {x : UA E a} (hx : x ∈ locU a w) : y * x * y⁻¹ ∈ locU a w := by
  simp only [locU, finU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, map_mul, map_inv] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  exact ⟨by simp [h1], fun u hu => by simp [h2 u hu]⟩

theorem exists_locU_mul_comm {E : Type} [Field E] [NumberField E] [IsCMField E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (hw : IsSplitAt w) (g : UA E a) :
    ∃ x ∈ locU a w, ∃ y : UA E a, g = x * y ∧ ∀ z ∈ locU a w, y * z = z * y := by
  have hb := (GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph E a w hw).1
  obtain ⟨x, hx⟩ := hb.2 (cLoc w g)
  have hx' : cLoc w (x : UA E a) = cLoc w g := hx
  refine ⟨x, x.2, (x : UA E a)⁻¹ * g, by group, fun z hz => ?_⟩
  have hy : cLoc w ((x : UA E a)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hx', inv_mul_cancel]
  have hc := locU_conj_mem w ((x : UA E a)⁻¹ * g) hz
  have he : (⟨_, hc⟩ : locU a w) = ⟨z, hz⟩ := hb.1 (by
    change cLoc w (_ * z * _) = cLoc w z
    rw [map_mul, map_mul, map_inv, hy]; group)
  have he' := congrArg Subtype.val he
  simp only at he'
  calc (x : UA E a)⁻¹ * g * z = ((x : UA E a)⁻¹ * g * z * ((x : UA E a)⁻¹ * g)⁻¹) * ((x : UA E a)⁻¹ * g) := by group
    _ = z * ((x : UA E a)⁻¹ * g) := by rw [he']

theorem span_comp_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, φ ∈ ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 := by
  intro E _ _ _ a U hU w hw σ hσ φ hφ
  set S := ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
    f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 with hS
  have hSU : S ≤ U := iSup_le fun f => by
    rintro _ ⟨v, rfl⟩; exact f.2.1 v
  obtain ⟨-, f0, hf0, hf0U, hf0e⟩ := hσ
  have hS0 : S ≠ ⊥ := by
    intro h
    apply hf0
    ext v
    have : f0 v ∈ S := (le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
      f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) ⟨f0, hf0U, hf0e⟩) ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at this
    simp [this]

  have hloc : ∀ x : locU a w, ∀ ψ ∈ S, RU E a x ψ ∈ S := by
    intro x ψ hψ
    rw [hS] at hψ
    refine Submodule.iSup_induction _ (motive := fun ψ => RU E a x ψ ∈ S) hψ ?_ ?_ ?_
    · intro f ψ hψ
      obtain ⟨v, rfl⟩ := hψ
      rw [← f.2.2 x v]
      exact le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
        f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) f ⟨_, rfl⟩
    · simp
    · intro ψ₁ ψ₂ h₁ h₂; simpa only [map_add] using add_mem h₁ h₂

  have hcen : ∀ y : UA E a, (∀ z ∈ locU a w, y * z = z * y) → ∀ ψ ∈ S, RU E a y ψ ∈ S := by
    intro y hy ψ hψ
    rw [hS] at hψ
    refine Submodule.iSup_induction _ (motive := fun ψ => RU E a y ψ ∈ S) hψ ?_ ?_ ?_
    · intro f ψ hψ
      obtain ⟨v, rfl⟩ := hψ
      let f' : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
          f (σ.ρ (cLoc w x) v) = RU E a x (f v)} :=
        ⟨RU E a y ∘ₗ f.1, fun v => hU.stable y _ (f.2.1 v), fun x v => by
          simp only [LinearMap.comp_apply]
          rw [f.2.2 x v, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, hy x x.2]⟩
      exact le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
        f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) f' ⟨v, rfl⟩
    · simp
    · intro ψ₁ ψ₂ h₁ h₂; simpa only [map_add] using add_mem h₁ h₂
  have hstab : ∀ g, ∀ ψ ∈ S, RU E a g ψ ∈ S := by
    intro g ψ hψ
    obtain ⟨x, hx, y, rfl, hy⟩ := exists_locU_mul_comm a w hw g
    rw [map_mul, mul_apply_eq_comp]
    exact hloc ⟨x, hx⟩ _ (hcen y hy ψ hψ)
  rcases hU.irred S hSU hstab with h | h
  · exact absurd h hS0
  · rw [h]; exact hφ

end GlobalTheory.Cong
end
end
