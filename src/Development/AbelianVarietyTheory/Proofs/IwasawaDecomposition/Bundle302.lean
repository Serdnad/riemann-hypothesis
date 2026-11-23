module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle284
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle293
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
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeH
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.Mem.RaySplit

open GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

theorem exists_span_eq_of_splits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)) (hR : GlobalTheory.Mem.Fld.IsRayField K L 𝔮) (𝔭 : HeightOneSpectrum (𝓞 K)) (hnd : ¬ 𝔭.asIdeal ∣ 𝔮)
    (hs : (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L) :
    ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  have := hR.1
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hnd (Ideal.dvd_iff_le.2 (le_sup_right.trans (𝔭.isMaximal.eq_of_le h le_sup_left).symm.le))
  obtain ⟨σ, P, hP, hPo, hσ⟩ := exists_isFrob L 𝔭
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hef := (GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭).1 hs P ⟨hP, hPo⟩
  have hf : 𝔭.asIdeal.inertiaDeg' P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  have hN : Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot, hf, pow_one]
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI := Ideal.Quotient.field P
  letI := Fintype.ofFinite (𝓞 L ⧸ P)
  have hpow : ∀ x : 𝓞 L, x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := fun x => by
    rw [← Ideal.Quotient.eq, map_pow, ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hin : InInertia L 𝔭 σ := ⟨P, hP, hPo, fun x => by
    have := add_mem (hσ x) (hpow x)
    rwa [sub_add_sub_cancel] at this⟩
  have hσ1 : σ = 1 := hR.2.1 𝔭 hnd σ hin
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ 𝔭.asIdeal = 1 := fun χ => by
    rw [heckeIdeal_asIdeal, heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ⟨P, hP, hPo, hσ⟩, hσ1, map_one, Units.val_one]
  obtain ⟨α, β, hab, he⟩ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).1 hχ
  have hα : α ∈ 𝔭.asIdeal * Ideal.span {β} := he ▸ Ideal.mem_span_singleton_self α
  obtain ⟨π, hπ, rfl⟩ := Ideal.mem_mul_span_singleton.1 hα
  have hβ0 : Ideal.span {β} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hab.2.1
  have hsp : 𝔭.asIdeal = Ideal.span {π} := by
    refine mul_right_cancel₀ hβ0 ?_
    rw [he, Ideal.span_singleton_mul_span_singleton]
  refine ⟨π, hsp, ?_⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hab.2.2.2.1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have h1 : (π - 1) * β ∈ 𝔮 := by
    have := hab.2.2.2.2.1
    rwa [show π * β - β = (π - 1) * β by ring] at this
  have h2 : π - 1 = c * ((π - 1) * β) + (π - 1) * j := by
    linear_combination (π - 1) * hij.symm
  rw [h2]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hj)

end GlobalTheory.Mem.RaySplit
end

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SJ.PairMain

theorem op_ramCrd_eq {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : St.LevelSubgroupCharacter) (w u : D.what₂.Word) (hw : w = u)
    (p : PerW St hK w) (q : PerW St hK u) (hpq : HEq p q) {n : ℕ} (b : Fin n → (D.mem w).A.Mram) (c : Fin n → ℂ)
    (φ : (D.mem u).A.Mram) (hc : HEq (∑ i, c i • b i) φ) (T : Cu St u hK)
    (hT : colDictL St q.Tr hK T = ((φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    (((p.op (ramCrd b c) : HHX St)) : L2X St) = PuFun St u hK q.Dt T := by
  subst hw
  obtain rfl := eq_of_heq hpq
  obtain rfl := eq_of_heq hc
  have h1 : ramCrd b c = Submodule.inclusion inf_le_left (∑ i, c i • b i) := by
    show Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ b c) = _
    rw [Fintype.linearCombination_apply]
    rfl
  have h2 : (colDict St p.Tr hK p.hI p.hB).symm (Submodule.inclusion inf_le_left (∑ i, c i • b i)) = T := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [colDict_apply, hT]
    rfl
  rw [h1]
  simp only [PerW.op, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h2]
  rfl

theorem pair_step : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (fc X.zs).Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin ((fc X.zs).Dc.a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (R.wU u) = u) → (fc X.zs).Sp = spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (R.wU u) i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) → ∀ (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (sEEc : X.EE →ₗ⋆[ℂ] Tw s (HHX St)), HEq sEE sEEc → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (κ₀ : ℂ), κ₀ ≠ 0 → (∀ F, Tw.out (sEEc (M.eR F)) = κ₀ • conjHH St G (j F)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu St u hK), colDictL St (pw u).Tr hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR F), (fc X.zs).Sp.Pu (R.wU u) (cjv s (M.cφ u φ))⟫_ℂ = cj s (κ * ⟪((conjHH St G (j F) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T⟫_ℂ) := by
  intro D Bs A X fc s R cr M St G hK pw wdD bR hw hSp hb
  generalize (fc X.zs).Sp = SP at hSp ⊢
  subst hSp
  intro sEE sEEc hE j κ₀ hκ₀ hout u
  obtain rfl := eq_of_heq hE
  refine ⟨starRingEnd ℂ κ₀, (map_ne_zero _).2 hκ₀, ?_⟩
  intro F φ T hT
  refine (Pair.inner_tw_of_smul (E := HHX St) s (sEE (M.eR F) : Tw s (HHX St))
    ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ)) : Tw s (HHX St)) κ₀
    ((conjHH St G (j F) : HHX St)) (hout F)).trans ?_
  congr 2
  have hcc : cjVec s _ (cjv s (M.cφ u φ)) = M.cφ u φ := funext fun i => cj_cj s _
  have hP : Tw.out (s := s) ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ))) =
      (pw (wdD (R.wU u))).op (ramCrd (bR (R.wU u)) (M.cφ u φ)) :=
    (spOf_Pu s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR (R.wU u) (cjv s (M.cφ u φ))).trans (by rw [hcc])
  have key := op_ramCrd_eq St hK _ u (hw u) _ _ (congr_arg_heq pw (hw u)) (bR (R.wU u)) (M.cφ u φ) _
    (Pair.sum_coord_heq M u _ (hw u) (bR (R.wU u)) (hb u) φ) T hT
  rw [Submodule.coe_inner]
  exact congrArg _ ((congrArg Subtype.val hP).trans key)

end GlobalTheory.Mem.SJ.PairMain
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocM.FrameBC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X}

theorem tv_sum' {κ : Type} (s : Finset κ) (f : κ → TanM x t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum]
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

def Full {κ : Type} [Fintype κ] (v : κ → TanM x t.G) : Prop :=
  ∀ n : TanM x t.G, ∃! a : κ → S, n = ∑ k, a k • v k

theorem full_equiv {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ' ≃ κ) {v : κ → TanM x t.G} (hv : Full v) :
    Full (fun i => v (e i)) := fun n => by
  obtain ⟨a, ha, hu⟩ := hv n
  refine ⟨fun i => a (e i), ha.trans (e.sum_comp (fun k => a k • v k)).symm, fun b hb => ?_⟩
  have := hu (fun k => b (e.symm k)) (hb.trans (by
    rw [← e.sum_comp]; simp only [Equiv.symm_apply_apply]))
  funext i; rw [← this]; simp

theorem full_iff {m : ℕ} {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → TanM x t.G}
    (e : ∀ i, pushHom h (epsR S) (u i) = tv (v i)) : IsLieBasis u ↔ Full v := by
  have key : ∀ a p n, pushHom h (epsR S) p = tv n → (IsLieComb a u p ↔ n = ∑ k, a k • v k) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum']; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum']; rfl)⟩
  refine ⟨fun hu n => ?_, fun hv => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv n)
    simpa only [key _ p n hp] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem n))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using hv (mkT _ ((isTangent_iff h p).1 hp))

def resM (ψ : S →+* T) (n : TanM x t.G) : TanM (spMap ψ ≫ x) t.G := tanOf (isTan_map ψ rfl (isTan_tv n))

theorem full_bc {m : ℕ} (ψ : S →+* T) {v : Fin m → TanM x t.G} (hv : Full v) : Full fun i => resM ψ (v i) := by
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  choose u hu using fun i => push_surj h₀ (tv (v i))
  choose u' hu' using fun i => push_surj h (tv (resM ψ (v i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (full_iff h hu').1 (Chart.frameLieBCR _ ((full_iff h₀ hu).2 hv) ψ (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (PullbackSections.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

variable {l : Level H} (c : Coeff l) [Algebra c.F S]

theorem eig_iff (τ : E →+* ℂ) (n : TanM x t.G) :
    (∀ a : 𝓞 E, (tv n).left ≫ (t.act.act a).left = spMap (epsMul (algebraMap c.F S (embK c τ a))) ≫ (tv n).left) ↔
      IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n :=
  forall_congr' fun _ => ⟨fun h => tan_ext h, fun h => congrArg (fun V => (tv V).left) h⟩

theorem eig_comb' (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hv i b, smul_comm]

theorem full_of_eig {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hv : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hb : ∀ τ n, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n → ∃! a : Fin (d τ) → S, n = ∑ i, a i • v τ i) :
    Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2) := by
  classical
  intro m
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM x t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => hb τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), a k.1 k.2 • v k.1 k.2
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), b k • v k.1 k.2 := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • v τ i)
      (fun τ => eig_comb' c τ _ (fun i => hv τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

theorem eig_of_full {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hE : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hfull : Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2)) (τ : E →+* ℂ) (w : TanM x t.G)
    (hm : IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) w) : ∃! a : Fin (d τ) → S, w = ∑ i, a i • v τ i := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hproj : proj ρ (embK c) α τ w = w := by
    have := proj_sum_eig ρ (embK c) α hinj (fun σ' => if σ' = τ then w else 0)
      (fun σ' => by
        split_ifs with h
        · subst h; exact hm
        · exact fun a => by simp) τ
    simpa [Finset.sum_ite_eq'] using this
  obtain ⟨A, hA, hAu⟩ := hfull w
  have hcomp : proj ρ (embK c) α τ w = ∑ i, A ⟨τ, i⟩ • v τ i := by
    have h1 := proj_sum_eig ρ (embK c) α hinj (fun σ' => ∑ i, A ⟨σ', i⟩ • v σ' i)
      (fun σ' => eig_comb' c σ' _ (fun i => hE σ' i) _) τ
    rw [← Fintype.sum_sigma (fun k : (Σ σ : E →+* ℂ, Fin (d σ)) => A k • v k.1 k.2), ← hA] at h1
    exact h1
  refine ⟨fun i => A ⟨τ, i⟩, hproj.symm.trans hcomp, fun b hb => ?_⟩
  have hb : w = ∑ i, b i • v τ i := hb
  let B : (Σ σ : E →+* ℂ, Fin (d σ)) → S := fun k => if h : k.1 = τ then b (h ▸ k.2) else 0
  have hB : w = ∑ k, B k • v k.1 k.2 := by
    rw [Fintype.sum_sigma, hb, Finset.sum_eq_single τ]
    · exact Finset.sum_congr rfl fun i _ => by simp [B]
    · intro σ _ hσ
      exact Finset.sum_eq_zero fun i _ => by simp [B, hσ]
    · intro h; exact absurd (Finset.mem_univ τ) h
  have := hAu B hB
  funext i
  have := congrFun this ⟨τ, i⟩
  simpa [B] using this

end GlobalTheory.LocM.FrameBC


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in
theorem GlobalTheory.LocM.isFrame_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  intro E _ _ _ H Dw l c X t R S _ _ f φ x u hu
  letI : Algebra c.F R := f.toAlgebra
  letI : Algebra c.F S := (φ.comp f).toAlgebra
  let v : ∀ τ, Fin (Dw.mult τ) → TanM x t.G := fun τ i => tanOf (hu.1 τ i).1
  have he : ∀ τ i (a : 𝓞 E), u.bc φ τ i ≫ (t.act.act a).left =
      spMap (epsMul ((φ.comp f) (embK c τ a))) ≫ u.bc φ τ i := fun τ i a => by
    show (spMap (dualMap φ) ≫ u τ i) ≫ _ = _ ≫ spMap (dualMap φ) ≫ u τ i
    rw [Category.assoc, (hu.1 τ i).2 a, ← Category.assoc, Formalism.L2.Pj.FrCov.eps_dual, Category.assoc, RingHom.comp_apply]
  have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (hu.1 τ i).2) fun τ n hn => by
    exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (hu.2 τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
  have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM φ (v k.1 k.2) := by
    have h := full_equiv (eB Dw).symm (full_bc φ (full_equiv (eB Dw) h1))
    exact (funext fun k => congrArg (fun j : IxB Dw => resM φ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
  refine ⟨fun τ i => ⟨isTan_map φ rfl (hu.1 τ i).1, he τ i⟩, fun τ w hw hwe => ?_⟩
  have h3 := eig_of_full c (fun τ i => resM φ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
    ((eig_iff c τ _).1 hwe)
  exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM φ (v τ i)) a (tanOf hw)).2 h3
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrameOffPlace

theorem swap_one_tmul_apply {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (ι : E ⊗[F1] FiniteAdeleRing (𝓞 F1) F1 →+* FiniteAdeleRing (𝓞 E) E)
    (hι : ∀ x a, ι (x ⊗ₜ[F1] a) = algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F1 E a)
    (a : FiniteAdeleRing (𝓞 F2) F2) (Q : HeightOneSpectrum (𝓞 E)) :
    ι (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E
        ((GlobalTheory.Mem.R3.swapCast h).symm ((1 : E) ⊗ₜ[F2] a))) Q =
      GlobalTheory.AdeleBaseChange.locMap F2 Q (a (Q.under (𝓞 F2))) := by
  subst h
  have e : (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).symm ((1 : E) ⊗ₜ[F1] a) = a ⊗ₜ[F1] (1 : E) := by
    apply (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [e, Algebra.TensorProduct.comm_tmul, hι, map_one, one_mul, GlobalTheory.AdeleBaseChange.adMap_apply]

end GlobalTheory.FrameOffPlace

namespace GlobalTheory.FrameOffPlace



theorem cpt_conj_finE_eq_one : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b) := by
  classical
  intro D V n hF P β hP s κ hκ Q hQ a b
  obtain ⟨⟨β0, β0', h1, -, hβ⟩, -⟩ := hP
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := Q.under _
  have hvs : v ∉ ({s.v} : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) := by
    intro h
    exact hQ (congrArg HeightOneSpectrum.asIdeal (Set.mem_singleton_iff.1 h))
  let f : ReciprocityTheory.Aut.AL D.host.E →+* Q.adicCompletion D.host.E :=
    (GlobalTheory.StdFrames.cpt Q).comp ((Formalism.IndefR.Lev.swapAE D).comp (GlobalTheory.Mem.R3.swapCast hF).symm.toRingHom)
  have hf0 : ∀ c : ReciprocityTheory.Aut.AFplus D.host.E, ReciprocityTheory.Aut.evalAt D.host.E v c = 0 →
      f ((1 : D.host.E) ⊗ₜ c) = 0 := by
    intro c hc
    have e := swap_one_tmul_apply hF (GlobalTheory.StdFrames.toAd D) (GlobalTheory.StdFrames.toAd_spec D) c Q
    have e' : f ((1 : D.host.E) ⊗ₜ c) = GlobalTheory.AdeleBaseChange.locMap _ Q (c (Q.under _)) := e
    rw [e']
    change GlobalTheory.AdeleBaseChange.locMap _ Q (ReciprocityTheory.Aut.evalAt D.host.E v c) = 0
    rw [hc, map_zero]
  have hsurj : Function.Surjective (ReciprocityTheory.Aut.evalAt D.host.E v) := fun c =>
    ⟨⟨Pi.single v c, (Filter.eventually_cofinite_ne v).mono fun w hw => by
      rw [Pi.single_eq_of_ne hw]; exact zero_mem _⟩, by
      change Pi.single v c v = c
      rw [Pi.single_eq_same]⟩
  have hker : ∀ y y' : ReciprocityTheory.Aut.AL D.host.E,
      ReciprocityTheory.Aut.compAt D.host.E v y = ReciprocityTheory.Aut.compAt D.host.E v y' → f y = f y' := by
    intro y y' h
    have hm : y - y' ∈ RingHom.ker
        (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield D.host.E) D.host.E) (ReciprocityTheory.Aut.evalAt D.host.E v)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact h
    rw [Algebra.TensorProduct.lTensor_ker _ hsurj] at hm
    have hle : RingHom.ker (ReciprocityTheory.Aut.evalAt D.host.E v) ≤ (RingHom.ker f).comap
        (Algebra.TensorProduct.includeRight : ReciprocityTheory.Aut.AFplus D.host.E →ₐ[maximalRealSubfield D.host.E] ReciprocityTheory.Aut.AL D.host.E) := by
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hf0 c hc
    have h2 := Ideal.map_le_iff_le_comap.2 hle hm
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2
  have hK : (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f = 1 := by
    have e := hκ v hvs
    ext i j
    have e2 := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at e2 ⊢
    rw [Matrix.one_apply] at e2 ⊢
    split_ifs at e2 ⊢
    · rw [hker _ 1 (e2.trans (map_one _).symm), map_one]
    · rw [hker _ 0 (e2.trans (map_zero _).symm), map_zero]
  let g : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* Q.adicCompletion D.host.E :=
    (GlobalTheory.StdFrames.cpt Q).comp (Formalism.IndefR.Lev.swapAE D)
  have hmain : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) = 1 := by
    have e1 : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map (Formalism.IndefR.Lev.swapAE D) := rfl
    have e2 : ∀ {k l : Type} (M : Matrix k l (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
        (M.map (Formalism.IndefR.Lev.swapAE D)).map (GlobalTheory.StdFrames.cpt Q) = M.map g := fun M => rfl
    have e3 : ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.Mem.R3.swapCast hF).symm).map g =
        (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f := rfl
    rw [e1, e2, hβ κ, Matrix.map_mul, Matrix.map_mul, e3, hK, Matrix.mul_one, ← Matrix.map_mul, h1,
      Matrix.map_one _ (map_zero g) (map_one g)]
  have e : (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)).map (GlobalTheory.StdFrames.cpt Q) := by
    have hinv : (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * β.val.map (GlobalTheory.StdFrames.cpt Q) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    calc (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q)
        = (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) *
            β.val.map (GlobalTheory.StdFrames.cpt Q) := by
          rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
      _ = 1 := by rw [hmain, Matrix.mul_one, hinv]
      _ = _ := (Matrix.map_one _ (map_zero _) (map_one _)).symm
  exact congrFun (congrFun e a) b

end GlobalTheory.FrameOffPlace
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isFixedBasisReductionMap_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) (c : G0g D.nd), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → FixRed X red b → ∃ b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (fun k => c⁻¹ * red k * c) b' := by
  first | exact @GlobalTheory.Mem.SRe.fixRed_conj | exact GlobalTheory.Mem.SRe.fixRed_conj | (intros; apply GlobalTheory.Mem.SRe.fixRed_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smooth_vectors_inner_product : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ φ, IsTest φ → ∀ w ∈ smSub G (trRep σ P), ∀ f : Lp ℂ 2 ν, ⟪f, A (gard ε σ φ w)⟫_ℂ = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪f, A (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  first | exact @GlobalTheory.SmVec.inner_l2_gard | exact GlobalTheory.SmVec.inner_l2_gard | (intros; apply GlobalTheory.SmVec.inner_l2_gard <;> assumption)
end
