module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle387
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin



noncomputable section
namespace GlobalTheory.LevelOffS

variable {D : D7}

theorem valued_algebraMap {v : GlobalTheory.FinPl.Pl D} (y : D.host.F) :
    Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) y) = v.valuation D.host.F y :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y

theorem inv_int {v : GlobalTheory.FinPl.Pl D} {c : 𝓞 D.host.F} (hc : c ∉ v.asIdeal) :
    evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (algebraMap (𝓞 D.host.F) D.host.F c)⁻¹) ∈
      v.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.intValuation c = 1 := le_antisymm (v.intValuation_le_one c)
    (not_lt.1 fun h => hc ((v.intValuation_lt_one_iff_mem c).1 h))
  have h2 : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (algebraMap (𝓞 D.host.F) D.host.F c)) = 1 := by
    rw [valued_algebraMap]
    exact (HeightOneSpectrum.valuation_of_algebraMap v c).trans h1
  rw [map_inv₀, map_inv₀, h2, inv_one]

theorem coe_ne_zero_of_nmem {v : GlobalTheory.FinPl.Pl D} {c : 𝓞 D.host.F} (hc : c ∉ v.asIdeal) :
    algebraMap (𝓞 D.host.F) D.host.F c ≠ 0 := by
  intro h
  apply hc
  rw [show c = 0 from IsFractionRing.injective (𝓞 D.host.F) D.host.F (h.trans (map_zero _).symm)]
  exact zero_mem _

theorem smul_pairA (r : D.host.F) (α : Af D.host.F) : r • pairA D.host.F 0 α = pairA D.host.F 0 (r • α) :=
  Prod.ext (smul_zero (A := Ainf D.host.F) r) rfl

theorem smul_vec_apply (c : 𝓞 D.host.F) {n : ℕ} (x : Fin n → D.host.E) (i : Fin n) :
    (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • x) i = algebraMap (𝓞 D.host.F) D.host.F c • x i := by
  rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
  congr 1

theorem latV_le_smul {S : HSp D} (Λ : Lat S) {v : GlobalTheory.FinPl.Pl D} (𝔪 : Ideal (𝓞 D.host.E)) {c : 𝓞 D.host.F}
    (hc : c ∉ v.asIdeal) (hcm : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ 𝔪) :
    latV S Λ (· = v) ≤ latV S (𝔪 • Λ) (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  rw [AddSubgroup.closure_le]
  rintro _ ⟨α, hα, hαv, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  set cF : D.host.F := algebraMap (𝓞 D.host.F) D.host.F c with hcF
  have hc0 : cF ≠ 0 := coe_ne_zero_of_nmem hc
  refine AddSubgroup.subset_closure ⟨α * algebraMap D.host.F (Af D.host.F) cF⁻¹, fun w => ?_, fun w hw => ?_, 1, rfl,
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • x, Submodule.smul_mem_smul hcm hx, ?_⟩
  · rw [map_mul]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (hα w) (inv_int hc)
    · rw [hαv w hw, zero_mul]
      exact zero_mem _
  · rw [map_mul, hαv w hw, zero_mul]
  · funext i
    rw [smul_vec_apply, one_mul, one_mul, ← TensorProduct.smul_tmul, smul_pairA]
    congr 2
    rw [Algebra.smul_def, mul_left_comm, ← map_mul, mul_inv_cancel₀ hc0, map_one, mul_one]

theorem finPart_finIn (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.FinPlLoc.finIn D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [GlobalTheory.FinPlLoc.finIn_tmul, GlobalTheory.FinPlLoc.finPart_pair]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem finIn_mem_idAt (z : Af D.host.F ⊗[D.host.F] D.host.E) : GlobalTheory.FinPlLoc.finIn D z ∈ idAt D (fun _ => True) := by
  unfold GlobalTheory.FinPl.idAt
  exact Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (GlobalTheory.FinPlLoc.infPart_finIn z),
    (Submodule.mem_iInf _).2 fun w => absurd trivial w.2⟩

theorem hatL_mono {n : ℕ} {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ ≤ Λ') :
    Formalism.L2.Herm.hatL (F := D.host.F) Λ ≤ Formalism.L2.Herm.hatL (F := D.host.F) Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_GfC_of_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {κ : GA D S} (h : κ ∈ grpAt S P) : κ ∈ GfC S := by
  unfold GlobalTheory.FinPl.grpAt at h
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at h
  show infHom S κ = 1
  apply Units.ext
  ext i j
  have h1 := GlobalTheory.FinPlLoc.infPart_of_idAt (h i j)
  rw [map_sub, sub_eq_zero] at h1
  change infPart D (mt S κ i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem finE_coe {S : HSp D} (κ : GA D S) :
    ((Lev.finE S κ : GL (Fin S.rank) (Lev.EAf D)) : Matrix (Fin S.rank) (Fin S.rank) (Lev.EAf D)) =
      (mt S κ).map ((Lev.swapAE D).comp (finPart D)) := rfl

theorem sub_mem_hatL_of_inK {S : HSp D} (Λ : Lat S) {v : GlobalTheory.FinPl.Pl D} (𝔪 : Ideal (𝓞 D.host.E)) {c : 𝓞 D.host.F}
    (hc : c ∉ v.asIdeal) (hcm : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ 𝔪) {κ : GA D S}
    (hκ : InK S Λ (· = v) κ) (x : Fin S.rank → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ((Lev.finE S κ : GL (Fin S.rank) (Lev.EAf D)) : Matrix (Fin S.rank) (Fin S.rank) (Lev.EAf D)) *ᵥ x - x ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  obtain ⟨z, hz⟩ : ∃ z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E, ∀ i, Lev.swapAE D (z i) = x i :=
    ⟨fun i => (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (x i), fun i => by
      show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
        ((Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (x i)) = x i
      generalize x i = y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]⟩
  set y0 : Fin S.rank → AE D := fun i => GlobalTheory.FinPlLoc.finIn D (z i) with hy0def
  have hφ : ∀ i, (Lev.swapAE D).comp (finPart D) (y0 i) = x i := fun i => by
    rw [RingHom.comp_apply, hy0def, finPart_finIn, hz]
  have hy0 : y0 ∈ latV S Λ (fun _ => True) := by
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D S Λ _ y0 (fun i => finIn_mem_idAt _) ?_
    convert hx using 1
    funext i
    exact hφ i
  set e := GlobalTheory.FinPlLoc.idem D (· = v) with he
  have hey : e • y0 ∈ latV S Λ (· = v) := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt _) hy0
  have hmv : mt S κ *ᵥ (e • y0) ∈ latV S Λ (· = v) := (hκ.2 _ (GlobalTheory.FinPlLoc.latV_idAt hey)).1 hey
  have hgrp := hκ.1
  unfold GlobalTheory.FinPl.grpAt at hgrp
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at hgrp
  have hN : ∀ i j, e * (mt S κ - 1) i j = (mt S κ - 1) i j := fun i j =>
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (by rw [Matrix.sub_apply]; exact hgrp i j)
  have hd : mt S κ *ᵥ (e • y0) - e • y0 = mt S κ *ᵥ y0 - y0 := by
    have h1 : ∀ w : Fin S.rank → AE D, mt S κ *ᵥ w - w = (mt S κ - 1) *ᵥ w := fun w => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [h1, h1, Matrix.mulVec_smul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hN i j]
  have hd' : mt S κ *ᵥ y0 - y0 ∈ latV S (𝔪 • Λ) (· = v) :=
    latV_le_smul Λ 𝔪 hc hcm (hd ▸ sub_mem hmv hey)
  have hfin := GlobalTheory.LatVHat.latV_mem_hatL D S (𝔪 • Λ) _ _ hd'
  convert hfin using 1
  funext i
  have hx' : x = ⇑((Lev.swapAE D).comp (finPart D)) ∘ y0 := funext fun j => (hφ j).symm
  rw [finE_coe, Pi.sub_apply, Pi.sub_apply, hx', ← RingHom.map_mulVec]
  change _ = (Lev.swapAE D).comp (finPart D) ((mt S κ *ᵥ y0 - y0) i)
  rw [Pi.sub_apply, map_sub]
  rfl

theorem exists_unit_mem_modul {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ G.pl.S0) : ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.modul := by
  classical
  have hex : ∀ u ∈ G.pl.S0, ∃ c ∈ u.asIdeal, c ∉ v.asIdeal := by
    intro u hu
    by_contra h
    push_neg at h
    have huv : u = v := HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top h)
    exact hv (huv ▸ hu)
  choose! f hf hfv using hex
  refine ⟨∏ u ∈ G.pl.S0, f u ^ G.pl.depth sc u, fun hmem => ?_, ?_⟩
  · obtain ⟨u, hu, hu'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact hfv u hu (v.isPrime.mem_of_pow_mem _ hu')
  · show _ ∈ ∏ u ∈ G.pl.S0, (G.pl.w u).asIdeal ^ G.pl.depth sc u
    rw [map_prod]
    apply Ideal.prod_mem_prod
    intro u hu
    rw [map_pow]
    apply Ideal.pow_mem_pow
    have h1 := G.pl.under_w hu
    have h2 : f u ∈ ((G.pl.w u).under (𝓞 D.host.F)).asIdeal := by rw [h1]; exact hf u hu
    exact h2

end GlobalTheory.LevelOffS


open GlobalTheory.LevelOffS in
theorem GlobalTheory.LevelOffS.inK_mem_lev : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → ∀ v, v ∉ G.pl.S0 → ∀ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ → κ ∈ lev G (.grid i 0) := by
  intro D hD T L μ0 hL sc G W M hM i hi v hv κ hκ
  obtain ⟨c, hc, hcm⟩ := exists_unit_mem_modul G hv
  refine Subgroup.mem_inf.2 ⟨mem_GfC_of_grpAt hκ.1, ?_⟩
  rw [Subgroup.mem_comap]
  show _ ∈ GlobalTheory.ChiGrid.congLev D.sp.cm (G.V (.grid i 0)).gram (G.Λ (.grid i 0)) G.modul
  rw [GlobalTheory.ChiGrid.mem_congLev]
  have hle : Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.grid i 0)) ≤ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid i 0)) :=
    hatL_mono Submodule.smul_le_right
  refine ⟨GlobalTheory.DefFree.finE_mem _ κ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun x hx => sub_mem_hatL_of_inK _ _ hc hcm hκ x hx⟩
  · have h1 := hle (sub_mem_hatL_of_inK _ _ hc hcm hκ x hx)
    have h2 := add_mem h1 hx
    rwa [sub_add_cancel] at h2
  · have h1 := hle (sub_mem_hatL_of_inK _ _ hc hcm (inK_inv hκ) _ hx)
    have h2 := add_mem h1 hx
    rw [sub_add_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2
    exact h2
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem partFixed_of_depFixed : DepFixed → DatumDep → PartFixed := by
  intro hD hd D q T L μ0 hL sc G W M hM ρ Φ u i h k hk g
  have hf := hd D q T L μ0 hL sc G W M hM ρ Φ ⟨i, h⟩
  have key := hD D q T L μ0 hL sc G W M hM i h (.chi i 0) (Or.inl rfl) _ hf 1 (one_mem _) k hk
  show liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ (g * k) = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ g
  rw [liftA_apply, liftA_apply]
  congr 1
  funext x
  congr 1
  show W.om (.chi i 0) (negGA _ (g * k), x) _ 0 = W.om (.chi i 0) (negGA _ g, x) _ 0
  have e : ((negGA _ (g * k), x) : GA D (G.pS (.chi i 0)) × GA D (G.pT (.chi i 0))) =
      (negGA _ g, x) * G.toPair (.chi i 0) 1 k := by
    show _ = (negGA _ g, x) * (negGA _ k, 1)
    rw [map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, map_mul, Module.End.mul_apply, key]

end GlobalTheory.Asc

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  intro hT h0 hB hJ D hq T L μ0 hL sc G W M hM v Ψ hΨ u hu hper
  obtain ⟨F, hE, ΓL, hG⟩ := hT D hq T L μ0 hL sc G W M hM v
  have key : ∀ k (h : 2 * k + 2 ≤ D.R.m), NZB W M v F Ψ u k h := by
    intro k
    induction k with
    | zero =>
      intro h
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h
        (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h)
    | succ k ih =>
      intro h
      have h' : 2 * k + 2 ≤ D.R.m := by omega
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu (k + 1) h
        (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h h' (ih h'))
  obtain ⟨r, hr⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hk : 2 * (r - 1) + 2 ≤ D.R.m := by omega
  have hk' : 2 * (r - 1) + 2 = D.R.m := by omega
  obtain ⟨ρ, Φ, hne⟩ := key (r - 1) hk
  refine ⟨ρ, Φ, ?_⟩
  let f : ∀ i, Fn G (.grid i 0) := fun i => if hi : i ≤ D.R.m then part W M ρ Φ u i hi else 0
  have hf : f D.R.m = thetaChi W M ρ Φ u := by
    simp only [f, dif_pos le_rfl]; rfl
  have := hE.top (r - 1) hk hk' Ψ f (hΨ.1 _ le_rfl) (by rw [hf, ← part_m]; exact hu ρ Φ _ le_rfl) (by
    simp only [f, dif_pos hk]; exact hne)
  rwa [hf] at this

end GlobalTheory.Asc
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory

namespace GlobalTheory.KernelApprox

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem thetaKO_sub (g : GA D S) (h : GA D T) (f f' : WO S T → ℂ) :
    thetaKO om g h f - thetaKO om g h f' = thetaKO om g h (f - f') := by
  simp only [thetaKO, map_sub, Pi.sub_apply]

theorem exists_kernel_approx (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om) (P : (WO S T → ℂ) → Prop)
    {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ)
    (hden : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → Φ ∈ GlobalTheory.Size.thetaLevel ψ S T U →
      ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε →
        ∃ X, P X ∧ X ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ) < ENNReal.ofReal ε) :
    ∃ a : ℕ, ∀ ε : ℝ, 0 < ε → ∃ X, P X ∧ ∀ g h,
      ‖thetaKO om g h X - thetaKO om g h Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a := by
  obtain ⟨a, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne S T
  obtain ⟨C, hC0, hC⟩ := (H _ _ rfl rfl).real ψ hθ hU
  refine ⟨a, fun ε hε => ?_⟩
  have hK : 0 < (C + 1) * 4 ^ a := by positivity
  obtain ⟨X, hPX, hXU, hsob⟩ := hden U hU hΦU μ 𝓕 hμ d (ε / ((C + 1) * 4 ^ a)) (div_pos hε hK)
  refine ⟨X, hPX, fun g h => ?_⟩
  have hΨ : X - Φ ∈ GlobalTheory.Size.thetaLevel ψ S T U := Submodule.sub_mem _ hXU hΦU
  rw [thetaKO_sub]
  obtain ⟨-, hb⟩ := hC _ _ _ hω μ 𝓕 hμ (X - Φ) hΨ
  have hsr : (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal ≤ ε / ((C + 1) * 4 ^ a) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsob.le
    rwa [ENNReal.toReal_ofReal (div_pos hε hK).le] at this
  obtain ⟨γ, hγ, h1⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight T h
  rw [← GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hΨ.1 γ hγ g h,
    ← GlobalTheory.Chain.LiftConv.thetaKO_left hω hΨ.1 (γ * g) γ' hγ' h]
  have hq1 := GlobalTheory.Grow.quotHeight_pos S g
  have hq2 := GlobalTheory.Grow.quotHeight_pos T h
  have hh1 := GlobalTheory.Grow.height_pos S (γ * g)
  have hh2 := GlobalTheory.Grow.height_pos T (γ' * h)
  have hs0 : 0 ≤ (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal := ENNReal.toReal_nonneg
  have hpow : (GlobalTheory.Grow.height S (γ * g) * GlobalTheory.Grow.height T (γ' * h)) ^ a ≤
      4 ^ a * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) a
  have hne : (C + 1) * 4 ^ a ≠ 0 := hK.ne'
  calc ‖thetaKO om (γ * g) (γ' * h) (X - Φ)‖
      ≤ C * (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal *
          (GlobalTheory.Grow.height S (γ * g) * GlobalTheory.Grow.height T (γ' * h)) ^ a := hb _ _
    _ ≤ (C + 1) * (ε / ((C + 1) * 4 ^ a)) * (4 ^ a * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a)) :=
        mul_le_mul (mul_le_mul (by linarith) hsr hs0 (by linarith)) hpow (pow_nonneg (mul_pos hh1 hh2).le a)
          (mul_nonneg (by linarith) (div_pos hε hK).le)
    _ = ((C + 1) * 4 ^ a) * (ε / ((C + 1) * 4 ^ a)) * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a) := by
        ring
    _ = ε * GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a := by
        rw [mul_div_cancel₀ _ hne]; ring

end GlobalTheory.KernelApprox

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.exists_rational_fullRank_besselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x ∈ {x : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E | LinearIndependent D.host.E x.transpose ∧ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ)}, (rat x : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) := by
  first | exact @GlobalTheory.Asc.FBx.exists_rat_eq_xLast | exact GlobalTheory.Asc.FBx.exists_rat_eq_xLast | (intros; apply GlobalTheory.Asc.FBx.exists_rat_eq_xLast <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.heisenbergVacuumCommutant_preserves_latticeVacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)), (∀ f, VacG ψ S T Γ f → ∀ w ∈ Ann ψ S T Γ, VacG ψ S T Γ (heisO ψ S T w f)) ∧ (∀ w : WO S T, (∀ u ∈ Γ, u.map (infPart D) = 0) → w.map (finPart D) = 0 → w ∈ Ann ψ S T Γ) ∧ ∀ (v : VolM D T.rank S.rank) f f₀, VacG ψ S T Γ f → VacG ψ S T Γ f₀ → ∀ w, w ∉ Ann ψ S T Γ → thPair v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
  first | exact @GlobalTheory.Asc.annVac | exact GlobalTheory.Asc.annVac | (intros; apply GlobalTheory.Asc.annVac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  first | exact @GlobalTheory.LinkInvTheta.link_inv_theta | exact GlobalTheory.LinkInvTheta.link_inv_theta | (intros; apply GlobalTheory.LinkInvTheta.link_inv_theta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ν : Measure (flagN d)) (𝓝 : Set (flagN d)), GlobalTheory.Per.IsUnitN S d.e ν 𝓝 → (IsClosed (jacGrp d : Set (GA D S)) ∧ ∀ μ : Measure (GA D S₀), μ.IsHaarMeasure → (semiMeas (flagN d) d.emb0 μ ν).IsHaarMeasure) ∧ IsClosed (besGrp d o : Set (GA D S)) ∧ ∀ μ : Measure (GA D A), μ.IsHaarMeasure → (semiMeas (flagN d) (embA d o) μ ν).IsHaarMeasure := by
  first | exact @GlobalTheory.MixPer.jacGrp_besGrp_haar | exact GlobalTheory.MixPer.jacGrp_besGrp_haar | (intros; apply GlobalTheory.MixPer.jacGrp_besGrp_haar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.MatCoefLevel

theorem matCoef_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, thPair μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1 := by
  intro D ψ hψ S T μ 𝓕 hcov f f₀ hf hf₀
  obtain ⟨U₁, hU₁, hl₁⟩ := hf.level
  obtain ⟨U₂, hU₂, hl₂⟩ := hf₀.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro w hw u hu hinf
  obtain ⟨hμ, h𝓕, -⟩ := hcov
  have hu₁ : heisO ψ S T u f = f := hl₁ u (AddSubgroup.mem_inf.1 hu).1 hinf
  have hu₂ : heisO ψ S T u f₀ = f₀ := hl₂ u (AddSubgroup.mem_inf.1 hu).2 hinf
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ w
  have e1 := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf hg u
  rw [hu₁, heisO_comm, hu₂] at e1
  have e2 : GlobalTheory.Ker.ipO μ 𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) =
      starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) := by
    unfold GlobalTheory.Ker.ipO
    rw [← integral_const_mul]
    congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  rw [e2] at e1
  have hw' : GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 := hw
  have h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) = 0 := by
    linear_combination e1
  have h4 : starRingEnd ℂ (ψ (symplO S T u w)) = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hw')
  have h5 : ψ (symplO S T u w) = 1 := by
    have h6 := congrArg (starRingEnd ℂ) h4
    rwa [Complex.conj_conj, map_one] at h6
  exact (psi_symplO_swap ψ _ _).1 h5

end GlobalTheory.MatCoefLevel

end
end
