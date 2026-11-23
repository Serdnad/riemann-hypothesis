module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle064
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle174
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.HaarStep



theorem integral_openOff_insert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)) (v : FinPl D), v ∉ Sf → ∀ μ : Measure (Gv A v), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L v) = 1 → ∀ (S' : Finset (FinPl D)), (∀ u, u ∈ S' ↔ u = v ∨ u ∈ Sf) → ∀ F : GA D A → ℂ, IntegrableOn F (openOff A L S') m → ∫ g in openOff A L S', F g ∂m = ∫ x in openOff A L Sf, (∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ) ∂m := by
  intro D A L hL m hm Sf v hv μ hμ hK S' hS' F hF
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.AdIsom.selfDual_isFullLattice hL
  have hne : ∀ u, u ∉ S' → u ≠ v := fun u hu h => hu ((hS' u).2 (Or.inl h))
  have memU : ∀ x, x ∈ openOff A L Sf ↔ x ∈ openOff A L S' ∧
      proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := by
    intro x
    constructor
    · intro h
      exact ⟨fun u hu => h u (fun hu' => hu ((hS' u).2 (Or.inr hu'))), h v hv⟩
    · rintro ⟨h1, h2⟩ u hu
      by_cases e : u = v
      · subst e; exact h2
      · exact h1 u (fun h => by rcases (hS' u).1 h with h | h; exact e h; exact hu h)
  have memV : ∀ (y : Gv A v) (x : GA D A), emb D.sp.cm.sig A.gram v y * x ∈ openOff A L S' ↔ x ∈ openOff A L S' := by
    intro y x
    refine forall_congr' fun u => imp_congr_right fun hu => ?_
    rw [map_mul, proj_emb_ne _ _ (hne u hu), one_mul]
  have isOpen_off : ∀ S : Finset (FinPl D), IsOpen (openOff A L S) := by
    intro S
    let H : Subgroup (GA D A) :=
      ⨅ u, ⨅ (_ : u ∉ S), (stabLoc D.sp.cm.sig A.gram L u).comap (proj D.sp.cm.sig A.gram u)
    have eH : (H : Set (GA D A)) = openOff A L S := by
      ext g; simp [H, openOff, Subgroup.mem_iInf]
    rw [← eH]
    refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) ?_ (isOpen_levelOpen _ _ L)
    intro g hg
    simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro u _
    exact (mem_levelOpen.1 hg) u
  have hUm : MeasurableSet (openOff A L Sf) := (isOpen_off Sf).measurableSet
  have hVm : MeasurableSet (openOff A L S') := (isOpen_off S').measurableSet
  have hKo : IsOpen (stabLoc D.sp.cm.sig A.gram L v : Set (Gv A v)) := isOpen_stabLoc _ _ L v
  have hright : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, μ.map (fun y => y * k) = μ := by
    intro k hk
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq,
      GlobalTheory.AdelicUnimod.modular_compact _ hKo (isCompact_stabLoc _ _ L v) hk, one_smul]
  have step1 : ∀ x ∈ openOff A L Sf,
      ∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ =
        ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ := by
    intro x hx
    have hkK : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := hx v hv
    set k := proj D.sp.cm.sig A.gram v x with hk
    set x' := x * (emb D.sp.cm.sig A.gram v k)⁻¹ with hx'
    have hx'1 : proj D.sp.cm.sig A.gram v x' = 1 := by
      rw [hx', map_mul, map_inv, proj_emb_self, mul_inv_cancel]
    have hxx : x = x' * emb D.sp.cm.sig A.gram v k := by rw [hx', inv_mul_cancel_right]
    have e : ∀ y, emb D.sp.cm.sig A.gram v y * x = x' * emb D.sp.cm.sig A.gram v (y * k) := by
      intro y
      have hc := (commute_emb D.sp.cm.sig A.gram y hx'1).eq
      calc emb D.sp.cm.sig A.gram v y * x = emb D.sp.cm.sig A.gram v y * x' * emb D.sp.cm.sig A.gram v k := by
            rw [mul_assoc, ← hxx]
        _ = x' * emb D.sp.cm.sig A.gram v y * emb D.sp.cm.sig A.gram v k := by rw [hc]
        _ = x' * emb D.sp.cm.sig A.gram v (y * k) := by rw [map_mul, mul_assoc]
    simp_rw [e]
    have h := integral_map_equiv (μ := μ) (MeasurableEquiv.mulRight k)
      (fun y => F (x' * emb D.sp.cm.sig A.gram v y))
    have hm' : Measure.map (MeasurableEquiv.mulRight k) μ = μ := hright k hkK
    rw [hm'] at h
    exact h
  rw [setIntegral_congr_fun hUm step1]

  have hec : Continuous (emb D.sp.cm.sig A.gram v) := continuous_emb _ _ v
  have hpc : Continuous (proj D.sp.cm.sig A.gram v) := continuous_proj _ _ v
  let Q : Set (GA D A × Gv A v) :=
    {q | (proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ stabLoc D.sp.cm.sig A.gram L v}
  have hQo : IsOpen Q := hKo.preimage (((hpc.comp continuous_fst).inv).mul continuous_snd)
  let f₂ : GA D A × Gv A v → ℂ := Q.indicator (fun q => (openOff A L S').indicator F q.1)
  let T : GA D A × Gv A v → GA D A × Gv A v := fun p => (emb D.sp.cm.sig A.gram v p.2 * p.1, p.2)
  have hT : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : Gv A v × GA D A => (p.1, emb D.sp.cm.sig A.gram v p.1 * p.2))
        (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × Gv A v → Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : Gv A v × GA D A → GA D A × Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : Gv A v × GA D A => (p.1, emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  have hCm : ∀ a : Gv A v, MeasurableSet {y : Gv A v | a⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v} :=
    fun a => (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : Gv A v, μ {y : Gv A v | a⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v} = 1 := by
    intro a
    rw [← hK]
    exact measure_preimage_mul μ a⁻¹ _
  have slice : ∀ w, (fun y => f₂ (w, y)) =
      {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}.indicator
        (fun _ => (openOff A L S').indicator F w) := by
    intro w; funext y
    rfl
  have hFV : Integrable ((openOff A L S').indicator F) m := (integrable_indicator_iff hVm).2 hF
  have hf₂m : AEStronglyMeasurable f₂ (m.prod μ) :=
    (hFV.aestronglyMeasurable.comp_fst).indicator hQo.measurableSet
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = (openOff A L S').indicator F w := by
    intro w
    rw [slice w, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have innerN : ∀ w, ∫ y, ‖f₂ (w, y)‖ ∂μ = ‖(openOff A L S').indicator F w‖ := by
    intro w
    have : (fun y => ‖f₂ (w, y)‖) =
        {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}.indicator
          (fun _ => ‖(openOff A L S').indicator F w‖) := by
      rw [show (fun y => ‖f₂ (w, y)‖) = fun y => ‖(fun y => f₂ (w, y)) y‖ from rfl, slice w]
      funext y
      exact norm_indicator_eq_indicator_norm _ y
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (integrable_prod_iff hf₂m).2 ⟨Filter.Eventually.of_forall fun w => ?_, ?_⟩
    · rw [slice w]
      refine (integrable_indicator_iff (hCm _)).2 ?_
      haveI : IsFiniteMeasure (μ.restrict
          {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}) :=
        isFiniteMeasure_restrict.2 (by rw [hμC]; exact ENNReal.one_ne_top)
      exact integrable_const _
    · simp_rw [innerN]
      exact hFV.norm
  have hf₁ : Integrable (f₂ ∘ T) (m.prod μ) := (hT.integrable_comp hf₂m).2 hf₂
  have hI : ∫ p, f₂ (T p) ∂(m.prod μ) = ∫ p, f₂ p ∂(m.prod μ) := by
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hf₂m), hT.map_eq]
  have hT1 : ∀ x y, f₂ (T (x, y)) = (openOff A L Sf).indicator (fun x => F (emb D.sp.cm.sig A.gram v y * x)) x := by
    intro x y
    have hp : (proj D.sp.cm.sig A.gram v (emb D.sp.cm.sig A.gram v y * x))⁻¹ * y =
        (proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, proj_emb_self, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    have hmem : T (x, y) ∈ Q ↔ proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := by
      show (proj D.sp.cm.sig A.gram v (emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v ↔ _
      rw [hp, inv_mem_iff]
    by_cases h2 : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v
    · rw [show f₂ (T (x, y)) = (openOff A L S').indicator F (emb D.sp.cm.sig A.gram v y * x) from
        Set.indicator_of_mem (hmem.2 h2) _]
      by_cases h1 : x ∈ openOff A L S'
      · rw [Set.indicator_of_mem ((memV y x).2 h1), Set.indicator_of_mem ((memU x).2 ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (memV y x).1 h1), Set.indicator_of_notMem (fun h => h1 ((memU x).1 h).1)]
    · rw [show f₂ (T (x, y)) = 0 from Set.indicator_of_notMem (mt hmem.1 h2) _,
        Set.indicator_of_notMem (fun h => h2 ((memU x).1 h).2)]
  calc ∫ g in openOff A L S', F g ∂m = ∫ w, (openOff A L S').indicator F w ∂m := (integral_indicator hVm).symm
    _ = ∫ p, f₂ p ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ p, f₂ (T p) ∂(m.prod μ) := hI.symm
    _ = ∫ x, ∫ y, f₂ (T (x, y)) ∂μ ∂m := integral_prod (f₂ ∘ T) hf₁
    _ = ∫ x, (openOff A L Sf).indicator (fun x => ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ) x ∂m := by
      congr 1; funext x
      simp_rw [hT1]
      by_cases h : x ∈ openOff A L Sf <;> simp [h]
    _ = ∫ x in openOff A L Sf, ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ ∂m := integral_indicator hUm

end GlobalTheory.Core.Rk.HaarStep
end
end

section

noncomputable section

namespace GlobalTheory.Core.Rk.BdSplit

section Abstract

open Formalism.UG GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}


open Classical in
def cosetInd (S : Finset (G ⧸ K)) : G → ℂ := fun g => if (g : G ⧸ K) ∈ S then 1 else 0

theorem cosetInd_mem {S : Finset (G ⧸ K)} (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) : cosetInd S ∈ Hecke ℂ K := by
  classical
  refine ⟨fun a b g => ?_, S.image Quotient.out, fun g hg => ?_⟩
  · have e : ((a * g * b : G) : G ⧸ K) = (a : G) • (g : G ⧸ K) := QuotientGroup.mk_mul_of_mem _ b.2
    have : (a : G) • (g : G ⧸ K) ∈ S ↔ (g : G ⧸ K) ∈ S :=
      ⟨fun h => by simpa using hS _ (inv_mem a.2) _ h, hS _ a.2 _⟩
    simp only [cosetInd, e, this]
  · have h : (g : G ⧸ K) ∈ S := by
      by_contra h
      exact hg (if_neg h)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ h, 1, k⁻¹, by rw [hk]; simp⟩

theorem heckeVec_cosetInd (ρ : Representation ℂ G V) (S : Finset (G ⧸ K)) (x : V) :
    heckeVec ρ K (cosetInd S) x = ∑ c ∈ S, ρ c.out x := by
  rw [heckeVec, finsum_eq_sum_of_support_subset (s := S)]
  · exact Finset.sum_congr rfl fun c hc => by simp [cosetInd, hc]
  · intro c hc
    by_contra h
    exact hc (by simp [cosetInd, show c ∉ S from h])

theorem norm_le_card {ι : Type} (ρ : Representation ℂ G V) {x : V} (l : V →ₗ[ℂ] ℂ) {C : ℝ}
    (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) (S : Finset ι) (g : ι → G) (a : ℂ)
    (h : ∑ c ∈ S, ρ (g c) x = a • x) : ‖a‖ ≤ S.card := by
  have hb : BddAbove (Set.range fun y => ‖l (ρ y x)‖) := ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
  set M := ⨆ y, ‖l (ρ y x)‖
  have hM : ∀ y, ‖l (ρ y x)‖ ≤ M := fun y => le_ciSup hb y
  have hM0 : 0 < M := (norm_pos_iff.2 h1).trans_le (hM 1)
  have key : ∀ y, ‖a‖ * ‖l (ρ y x)‖ ≤ S.card * M := fun y => by

    rw [← norm_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← h, map_sum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun c _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact hM _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have : M ≤ S.card * M / ‖a‖ := ciSup_le fun y => by rw [le_div_iff₀' h0]; exact key y
    rw [le_div_iff₀' h0] at this
    exact le_of_mul_le_mul_right this hM0

end Abstract

section Linear

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SatakeBound

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem norm_le_of_isSatVecGL {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (l : V →ₗ[ℂ] ℂ) {C : ℝ} (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) :
    ∀ β ∈ B, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = n := hx.2.2.1
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨φ, hφ, hφ1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at hφ1
  have hy := isSatVecGL_of_isSpherical hφ hφ0
  have hKO : KO (w.adicCompletion E) (Fin n) = KGL w (n := n) := SphCompletion.KO_completion w n
  have hb : HasBoundedSums (w.adicCompletion E) φ := by
    intro S hS
    have H := SatCompare.exists_eigenvalue_GL hx hy
    rw [← hKO] at H
    obtain ⟨c, e1, e2⟩ := H _ (cosetInd_mem hS)
    rw [heckeVec_cosetInd] at e1 e2
    have e3 : ∑ c ∈ S, φ c.out = c := by
      have := congrFun e2 1
      rw [Finset.sum_apply, Pi.smul_apply, hφ1, smul_eq_mul, mul_one] at this
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => congrArg φ (one_mul _).symm
    rw [e3]
    exact norm_le_card ρ l hC h1 S _ c e1
  have hs : IsBorelSph (w.adicCompletion E) (fun i : Fin n => (α i : ℂ) *
      (((resCard (w.adicCompletion E) : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ := by
    refine ⟨fun g k hk => congrFun (GlobalTheory.LGrp.mem_fixed.1 hy.2.1 k (hKO ▸ hk)) g, fun b hb' t ht => ?_⟩
    obtain ⟨y, -, rfl⟩ := (SphCompletion.isSpherical_iff E w n α φ).1 hφ
    have h := GlobalTheory.SatakeBound.Rep.law α y b hb' t ht 1
    rwa [hφ1, mul_one, mul_one] at h
  intro β hβ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hβ
  have hq : (0 : ℝ) < resCard (w.adicCompletion E) := by
    exact_mod_cast (GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard (w.adicCompletion E)).le
  have h2 := norm_le_pow hs hb i
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), ← Real.rpow_natCast] at h2
  rw [← le_div_iff₀ (Real.rpow_pos_of_pos hq _), ← Real.rpow_sub hq] at h2
  rw [← GlobalTheory.LFun.SatBoundGL.resCard_completion w]
  exact h2.trans_eq (congrArg _ (by ring))

end Linear

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem paramBound_split : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  rintro D A L - v hv par c ⟨⟨C, hC⟩, V, _, _, ρ, x, l, hx, -, hc⟩ h1 w h
  refine ⟨(hx w h).card, fun β hβ => ?_⟩
  rcases hx w h with ⟨-, e, -, hx⟩ | ⟨hw, -⟩
  · have hb := norm_le_of_isSatVecGL hx l (C := C) (fun y => (hc (e.symm y)) ▸ hC (e.symm y))
      (by rw [hc] at h1; rwa [map_one, ← map_one ρ]) β hβ
    refine hb.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith))
    exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm w).le
  · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)

end GlobalTheory.Core.Rk.BdSplit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.VacMove

variable {D : D7}

theorem mt_mul_inv' (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mem_ideal_mul_mul {m n k l : ℕ} (I : Ideal (AE D)) (A : Matrix (Fin m) (Fin n) (AE D))
    (u : Matrix (Fin n) (Fin k) (AE D)) (B : Matrix (Fin k) (Fin l) (AE D)) (hu : ∀ i j, u i j ∈ I) :
    ∀ i j, (A * u * B) i j ∈ I := by
  intro i j
  simp only [Matrix.mul_apply]
  exact I.sum_mem fun x _ => I.mul_mem_right _ (I.sum_mem fun y _ => I.mul_mem_left _ (hu y x))

theorem mem_ideal_mulVec {m n : ℕ} (I : Ideal (AE D)) (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D)
    (hy : ∀ i, y i ∈ I) : ∀ i, (A *ᵥ y) i ∈ I := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

def pull {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) u) (Formalism.L2.Theta.mt S g)

theorem smul_latV_mem (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a : D.host.E) (ha : a ∈ D.host.AA) :
    ∀ y ∈ GlobalTheory.FinPl.latV S L P, ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y ∈ GlobalTheory.FinPl.latA S L P := by
  intro y hy
  have key : GlobalTheory.FinPl.latV S L P ≤ (GlobalTheory.FinPl.latA S L P).comap
      (DistribSMul.toAddMonoidHom (Fin S.rank → AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D)) := by
    unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hP, b, hb, x, hx, rfl⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    show _ ∈ GlobalTheory.FinPl.latMul S {a | a ∈ D.host.AA} L P
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, x, hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  exact key hy

theorem mulVec_latA_mem (T : HSp D) (LT MT : Lat T) (P : Pl D → Prop) (h : GA D T) (hMT : IsSelfDualC T MT)
    (hmov : Moves T h LT MT P) : ∀ z ∈ GlobalTheory.FinPl.latA T MT P, Formalism.L2.Theta.mt T h⁻¹ *ᵥ z ∈ GlobalTheory.FinPl.latA T LT P := by
  intro z hz
  have key : GlobalTheory.FinPl.latA T MT P ≤ (GlobalTheory.FinPl.latA T LT P).comap (Matrix.mulVecLin (Formalism.L2.Theta.mt T h⁻¹)).toAddMonoidHom := by
    unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    set y' : Fin T.rank → AE D := fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] ((1 : D.host.E) * x i) with hy'def
    have hy' : y' ∈ GlobalTheory.FinPl.latV T MT P := AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, x, hx, rfl⟩
    have hent : ∀ i, y' i ∈ idAt D P := (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 T).2.2.2 MT y' hMT.1).1 hy' |>.1
    have hy'' : Formalism.L2.Theta.mt T h⁻¹ *ᵥ y' ∈ GlobalTheory.FinPl.latV T LT P := by
      rw [hmov _ (mem_ideal_mulVec _ _ _ hent), Matrix.mulVec_mulVec, mt_mul_inv', Matrix.one_mulVec]
      exact hy'
    have hgen : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y' := by
      funext i; simp [y', Algebra.TensorProduct.tmul_mul_tmul]
    show Formalism.L2.Theta.mt T h⁻¹ *ᵥ _ ∈ GlobalTheory.FinPl.latMul T {a | a ∈ D.host.AA} LT P
    rw [hgen, Matrix.mulVec_smul]
    exact smul_latV_mem T LT P a ha _ hy''
  exact key hz

theorem vac_of_moves : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (f : WO S T → ℂ), Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f) := by
  intro D ψ S T χS χT om hW LS LT hLS hLT P f hf g h MS MT hMS hMT hmS hmT
  unfold Vac IsLatVac at hf ⊢
  obtain ⟨hf1, hf2, hf3⟩ := hf
  have hmem : ∀ u ∈ latO S T (MS : Set _) (MT : Set _) P,
      pull g h u ∈ latO S T (LS : Set _) (LT : Set _) P := by
    intro u hu
    have hu' := (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S T MS MT hMS hMT P u).1 hu
    refine (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S T LS LT hLS hLT P _).2 ⟨?_, ?_⟩
    · exact mem_ideal_mul_mul (idAt D P) _ _ _ hu'.1
    · intro y hy
      have hent := ((((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 LS y hLS.1).1 hy).1
      have h1 : Formalism.L2.Theta.mt S g *ᵥ y ∈ GlobalTheory.FinPl.latV S MS P := (hmS y hent).1 hy
      have h2 := hu'.2 _ h1
      have h3 := mulVec_latA_mem T LT MT P h hMT hmT _ h2
      show (pull g h u) *ᵥ y ∈ _
      unfold pull
      rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hact : ∀ u : WO S T, actO S T g h (pull g h u) = u := by
    intro u
    unfold actO pull
    simp only [← Matrix.mul_assoc, mt_mul_inv', Matrix.one_mul]
    simp only [Matrix.mul_assoc, mt_mul_inv', Matrix.mul_one]
  have hhalf : ∀ e (u : WO S T), IsHalf e u → IsHalf e (pull g h u) := by
    intro e u hu i j
    unfold pull
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    linear_combination (Formalism.L2.Theta.mt T h⁻¹ i y * Formalism.L2.Theta.mt S g x j) * hu y x
  refine ⟨hW.om_pres (g, h) f hf1, ?_, ?_⟩
  · intro u hu
    have hw := hf2 _ (hmem u hu)
    have e1 := hW.om_heis g h (2 • (pull g h u)) f hf1
    have e2 : actO S T g h (2 • (pull g h u)) = 2 • u := by
      have := hact u
      unfold actO at this ⊢
      rw [two_nsmul, two_nsmul, Matrix.mul_add, Matrix.add_mul, this]
    rw [hw, e2] at e1
    exact e1.symm
  · intro e he u hu hhu
    have hw := hf3 e he _ (hmem u hu) (hhalf e u hhu)
    have e1 := hW.om_heis g h (pull g h u) f hf1
    have e2 : actO S T g h (pull g h u) = u := hact u
    rw [hw, e2] at e1
    exact e1.symm

end GlobalTheory.VacMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  first | exact @GlobalTheory.HatLatV.mem_latV_of_hatL | exact GlobalTheory.HatLatV.mem_latV_of_hatL | (intros; apply GlobalTheory.HatLatV.mem_latV_of_hatL <;> assumption)
end
