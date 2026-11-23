module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle483
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.ratio_invariant_in_K0 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, P.actQ g a * b = a * P.actQ g b) → ∃ c : ↥(K0 K), a = algebraMap ↥(K0 K) P.R.B c * b := by
  first | exact @GlobalTheory.Per.FracInv.tied_frac_invariant | exact GlobalTheory.Per.FracInv.tied_frac_invariant | (intros; apply GlobalTheory.Per.FracInv.tied_frac_invariant <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.Cyc.UnitGen

theorem gen {O R P : Type*} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup P] [Module O P]
    (f : R →ₐ[O] R) (hinj : Function.Injective (algebraMap O R))
    (hf : ∀ b, f b = b → ∃ x : O, b = algebraMap O R x) (e₀ t t' : P)
    (h0 : Submodule.span O {e₀} = ⊤) (htf : ∀ c : O, c • e₀ = 0 → c = 0)
    (ht : Submodule.span O {t} = ⊤) (r : R)
    (hr : r • ((1 : R) ⊗ₜ[O] t') = (1 : R) ⊗ₜ[O] e₀) :
    ∃ u : Oˣ, (1 : R) ⊗ₜ[O] t' = algebraMap O R u ⊗ₜ[O] t := by
  have hb : Function.Bijective (LinearMap.toSpanSingleton O P e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).2 htf, ?_⟩
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, h0]
  let φ : O ≃ₗ[O] P := LinearEquiv.ofBijective _ hb
  have hφ : ∀ c, φ c = c • e₀ := fun _ => rfl
  have h1 : φ.symm e₀ = 1 := by rw [LinearEquiv.symm_apply_eq, hφ, one_smul]
  obtain ⟨c, rfl⟩ := φ.surjective t'
  obtain ⟨w, rfl⟩ := φ.surjective t
  have hrc : r * algebraMap O R c = 1 := by
    have := congrArg (fun y => TensorProduct.rid O R (φ.symm.toLinearMap.lTensor R y)) hr
    simpa [TensorProduct.smul_tmul', h1, Algebra.smul_def, mul_comm] using this
  have hfr : f r = r := by
    have h2 : f r * algebraMap O R c = 1 := by
      rw [← f.commutes c, ← map_mul, hrc, map_one]
    calc f r = f r * (r * algebraMap O R c) := by rw [hrc, mul_one]
      _ = r * (f r * algebraMap O R c) := by ring
      _ = r := by rw [h2, mul_one]
  obtain ⟨c', rfl⟩ := hf r hfr
  have hc : c' * c = 1 := hinj (by rw [map_mul, hrc, map_one])
  obtain ⟨w', hw'⟩ := Submodule.mem_span_singleton.1 (ht ▸ Submodule.mem_top : e₀ ∈ Submodule.span O {φ w})
  have hw : w' * w = 1 := by
    apply φ.injective
    rw [← smul_eq_mul, map_smul, hw', hφ, one_smul]
  refine ⟨⟨c * w', c' * w, ?_, ?_⟩, ?_⟩
  · linear_combination (w' * w) * hc + hw
  · linear_combination (w' * w) * hc + hw
  · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← map_smul, smul_eq_mul,
      mul_assoc, hw, mul_one]

variable {l : ℕ} [Fact l.Prime]

theorem zl_wcb_injective : Function.Injective (algebraMap ℤ_[l] (WCb l)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero h
  · exact WittVector.p_nonzero l (Cb l) (eq_zero_of_pow_eq_zero h)

theorem ol_rw_injective (LL : FinExt l) : Function.Injective (algebraMap ↥(OL LL) (RW LL)) :=
  by
    haveI := GlobalTheory.Cyc.FontW.free_OL LL
    set_option synthInstance.maxHeartbeats 200000 in
      exact Algebra.TensorProduct.includeLeft_injective (S := ↥(OL LL)) zl_wcb_injective

theorem fixed_RW (LL : FinExt l) (b : RW LL) (hb : φRW LL b = b) :
    ∃ x : ↥(OL LL), b = algebraMap ↥(OL LL) (RW LL) x :=
  by
    haveI := GlobalTheory.Cyc.FontW.free_OL LL
    set_option synthInstance.maxHeartbeats 200000 in
      exact (GlobalTheory.Cyc.FontW.as_one (O := ↥(OL LL)) (frobW l) (GlobalTheory.ArtinSchreierWitt.main l).1
        (GlobalTheory.ArtinSchreierWitt.main l).2.1).2 b hb

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem of_tie {W : LocWach PD LL O v n} {RA R : Type} [CommRing RA] [CommRing R] [Algebra O RA]
    [Algebra O R] {inclR : RA →ₐ[O] R} {φR : R →ₐ[O] R} {gR : G → (R →ₐ[O] R)} {πA : RA}
    (E : EtTie W RA R inclR φR gR πA) (hO : Function.Injective (algebraMap O LL))
    (hinj : Function.Injective (algebraMap O R))
    (hf : ∀ b, φR b = b → ∃ x : O, b = algebraMap O R x)
    (hT : ∀ b, TWmap φR W.one b = b → ∃ t : ↥W.one.L.T, b = (1 : R) ⊗ₜ[O] t)
    (e : W.DD W.one) (t : ↥W.one.L.T) (hN : W.N W.one = Submodule.span (LetA O n) {e})
    (hφ : W.φD W.one e = e) (ht : Submodule.span O {(t : W.one.V)} = W.one.L.T) :
    ∃ u : Oˣ, E.jD W.one e = algebraMap O R u ⊗ₜ[O] t := by
  obtain ⟨e', e₀, h0, hj, hN'⟩ := E.one_e
  obtain ⟨t', ht'⟩ := hT (E.jD W.one e) (by rw [← E.jD_φ, hφ])
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    (show e' ∈ Submodule.span (LetA O n) {e} by
      rw [← hN, hN']; exact Submodule.mem_span_singleton_self _)
  have hne : (e₀ : W.one.V) ≠ 0 := by
    obtain ⟨x, hx, hxT⟩ := W.one_line
    intro h
    have hxm : x ∈ W.one.L.T := by rw [hxT]; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (h0 ▸ Submodule.mem_top : (⟨x, hxm⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀})
    have := congrArg Subtype.val hc
    rw [Submodule.coe_smul, h, smul_zero] at this
    exact hx this.symm
  rw [ht']
  refine gen φR hinj hf e₀ t t' h0 (fun c hc => ?_) ?_ (E.ioE (algebraMap _ W.EE a)) ?_
  · have := congrArg Subtype.val hc
    rw [Submodule.coe_smul, ← algebraMap_smul LL] at this
    exact hO (((smul_eq_zero.1 this).resolve_right hne).trans (map_zero _).symm)
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (show x ∈ Submodule.span O {(t : W.one.V)} from ht.ge hx)
    exact Submodule.mem_span_singleton.2 ⟨c, Subtype.ext hc⟩
  · rw [← ht', ← E.jD_smul, algebraMap_smul, ha, hj]

end Gen

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (e : W.DD W.one) (t : ↥W.one.L.T), W.N W.one = Submodule.span (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) {e} → W.φD W.one e = e → Submodule.span ↥(OL LL) {(t : W.one.V)} = W.one.L.T → ∃ u : (↥(OL LL))ˣ, E.jD W.one e = ((u : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (1 : WCb l) : RW LL) ⊗ₜ[↥(OL LL)] t := by
  intro D HW F l _ K s LL h W E e t hN hφ ht
  exact of_tie E Subtype.val_injective (ol_rw_injective LL) (fixed_RW LL)
    (GlobalTheory.Cyc.FontW.as_TW LL W.one).2 e t hN hφ ht

end GlobalTheory.Cyc.UnitGen
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.classSum_regroup_finerLevel_cosets : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  first | exact @GlobalTheory.ClassRefineBridge.sum_isReps_refine | exact GlobalTheory.ClassRefineBridge.sum_isReps_refine | (intros; apply GlobalTheory.ClassRefineBridge.sum_isReps_refine <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCharChange
open Formalism.IndefR.Lev

theorem ratMat_exists {D : D7} (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  have h := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨γE, -, e⟩ := Subgroup.mem_map.1 h
  exact ⟨γE, e.symm⟩

theorem flag_vals {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (hcg : ∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ))
    (hxq : ∀ PP ∈ L.Q, ∀ x, ∃ a, D.what₂.embLL a = ((L.xq PP x : ℂˣ) : ℂ)) (x) :
    ∃ a, D.what₂.embLL a = ((levFn β (flagL L) x : ℂˣ) : ℂ) := by
  have h1 : (flagL L).P.chi = 1 := rfl
  unfold levFn
  rw [h1, subgroupCharExtension_one_apply, one_mul]
  refine RingHom.mem_fieldRange.1 ?_
  simp only [Units.val_mul, Units.coe_prod]
  refine Subfield.mul_mem _ (Subfield.prod_mem _ fun PP hP => Subfield.prod_mem _ fun j hj => ?_)
    (Subfield.prod_mem _ fun PP hP => ?_)
  · obtain ⟨a, ha⟩ := hcg j (Finset.mem_range.1 hj) PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩
  · obtain ⟨a, ha⟩ := hxq PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩

end GlobalTheory.TwistCharChange
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardExtension

theorem map_incl_smul {O R R' M : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R]
    [Algebra O R'] [AddCommGroup M] [Module O M] (f : R →ₐ[O] R') (a : R) (y : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (a • y) =
      f a • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add (f := _), hx, hx']
  | tmul r u => simp [TensorProduct.smul_tmul']

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ TAinf inclR T) :
    inclR a • z ∈ TAinf inclR T := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨a • y, map_incl_smul inclR a y⟩

theorem NAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ NAinf W E T) :
    inclR a • z ∈ NAinf W E T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a', x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a * a', x, hx, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

theorem p5inf_of_sand (T : LocLat G Qp LL O) (c : RW) (m : ℕ) (hc : c = inclR (E.io W.X) ^ m)
    (h1 : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x))
    (h2 : ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)}) :
    wachInfiniteLevelJumpBound W E T m m := by
  subst hc
  simp only [GlobalTheory.NL.SandArb.map_mulLeft] at h1 h2
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := hz
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x x' hx hx' => rw [map_add (f := _), smul_add]; exact add_mem hx hx'
    | tmul r t =>
      have e : inclR (E.io W.X) ^ m • TensorProduct.map inclR.toLinearMap LinearMap.id (r ⊗ₜ[O] t) =
          inclR r • ((inclR (E.io W.X) ^ m) ⊗ₜ[O] t : TW RW T) := by
        simp [TensorProduct.smul_tmul', mul_comm]
      rw [e]
      exact NAinf_smul E T r (h2 t)
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hx, rfl⟩ := hz
      obtain ⟨y, hy⟩ := h1 x hx
      rw [smul_comm]
      exact TAinf_smul T a ⟨y, hy⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

theorem etale_comparison_of_wach_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hφ : ∀ y : TW RW T, TWmap φR T y = y ↔ ∃ t : ↥T.L.T, y = (1 : RW) ⊗ₜ[O] t) : p1et W E T := by
  obtain ⟨c, hc⟩ := GlobalTheory.WachTensor.exists_basis_jD E T ((W.N_base T hT).basis b)
  have hc' : ∀ j, c j = E.jD T (b j : W.DD T) := fun j => by
    rw [hc, IsBaseChange.basis_apply b (W.N_base T hT) j]; rfl
  refine ⟨⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_, fun y => ?_⟩, hφ⟩
  · have key : ∀ a : Fin r → LetA O n, x = ∑ j, a j • (b j : W.DD T) ↔
        (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • b j := by
      intro a
      rw [Subtype.ext_iff]
      simp
    refine ⟨fun j => b.repr ⟨x, hx⟩ j, (key _).2 (b.sum_repr ⟨x, hx⟩).symm, fun a ha => ?_⟩
    rw [(key a).1 ha, b.repr_sum_self]
  · refine ⟨fun j => c.repr y j, ?_, fun a ha => ?_⟩
    · show y = _
      simp only [← hc']
      exact (c.sum_repr y).symm
    · have ha' : y = ∑ j, a j • c j := by simpa only [← hc'] using ha
      rw [ha', c.repr_sum_self]

end Generic



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    p1eL D.loc D.locA HW F := by
  intro D HW F l _ K s LL h T hT
  refine ⟨?_, ?_⟩
  · obtain ⟨b⟩ := N_basis D HW F l K s LL h T hT
    exact etale_comparison_of_wach_basis _ T hT b (GlobalTheory.WittTensorFixed.main l K LL T).2.1
  · obtain ⟨m, h1, h2⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
    exact ⟨m, p5inf_of_sand _ T _ m rfl h1 h2⟩

end GlobalTheory.NL.NygaardExtension
end
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.ChebCyc

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private theorem tsum_logFactor_add_log_sub_one_isBigO_one (K : Type) [Field K] [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) + Real.log (s - 1))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hT := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have hr : ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ ≠ 0 := by
    simp [dedekindZeta_residue_ne_zero]
  have hL := ((Real.continuousAt_log hr).tendsto.comp hT).isBigO_one ℝ
  refine hL.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [Function.comp_apply]
  rw [norm_mul, _root_.GlobalTheory.Mem.ZetaPole.norm_dedekindZeta_eq_exp K hs]
  have hs1 : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hs1, Real.log_mul (sub_ne_zero.2 hs.ne') (Real.exp_pos _).ne', Real.log_exp]
  ring

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private theorem tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one (K : Type) [Field K]
    [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hN : ∀ P : HeightOneSpectrum (𝓞 K), 2 ≤ Ideal.absNorm P.asIdeal :=
    fun P => _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
  have hC := _root_.GlobalTheory.Mem.RayPrimes.logSum_sub_bounded (fun P : HeightOneSpectrum (𝓞 K) =>
    Ideal.absNorm P.asIdeal) hN (fun _ => 1) (fun _ => by simp)
    (fun s hs => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2)
  have hC' : (fun s : ℝ => (((∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine hC.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [Complex.ofReal_sub, Complex.ofReal_tsum, Complex.ofReal_tsum]
    congr 1
    · refine tsum_congr fun P => ?_
      rw [_root_.GlobalTheory.Mem.ZetaPole.ofReal_logFactor (by linarith [hN P]) (by linarith), one_mul]
    · refine tsum_congr fun P => ?_
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _), one_mul, Complex.ofReal_natCast,
        Complex.ofReal_neg]
  rw [← isBigO_norm_left]
  exact hC'.norm_left.congr_left fun s => Complex.norm_real _


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.ChebCyc.primeSum_add_log_isBigO : ∀ (K : Type) [Field K] [NumberField K], (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  intro K _ _
  refine ((tsum_logFactor_add_log_sub_one_isBigO_one K).sub
    (tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one K)).congr_left fun s => ?_
  ring

end GlobalTheory.ChebCyc
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.HeckeAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

theorem mem_conj {g : G} {t : K} :
    t ∈ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K ↔ g⁻¹ * (t : G) * g ∈ K := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, e⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    rw [← e]; simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem fix_eq {H : Subgroup K} {v : V} (hv : ∀ h ∈ H, ρ ((h : K) : G) v = v) {a b : K} (hab : (a : K ⧸ H) = b) :
    ρ (a : G) v = ρ (b : G) v := by
  have hm := QuotientGroup.eq.1 hab
  have : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
  rw [this, map_mul, Module.End.mul_apply, hv _ hm]

end GlobalTheory.HeckeAvg
end
end
