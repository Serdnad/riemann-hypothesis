module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

open GlobalTheory.Cong.LevelExt in
theorem UpperTheory.Gal.Gen.levFacts_pf :
    UpperTheory.Gal.Gen.LevFacts := by
  intro E _ _ _ a w₀ hw K hK J hJo hJc
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let s : GL (Fin a) (w₀.adicCompletion E) → UA E a := fun h => ((e.symm h : locU a w₀) : UA E a)
  have hs_mem : ∀ h, s h ∈ locU a w₀ := fun h => (e.symm h).2
  have hs_loc : ∀ h, cLoc w₀ (s h) = h := fun h => by
    rw [← he]
    exact e.apply_symm_apply h
  have hs_cont : Continuous s := continuous_subtype_val.comp e.symm.continuous
  have hs_eq : ∀ x ∈ locU a w₀, s (cLoc w₀ x) = x := fun x hx => by
    have := e.symm_apply_apply ⟨x, hx⟩
    rw [he] at this
    exact congrArg Subtype.val this
  have hcont := GlobalTheory.BCT.GlobLev.continuous_cLoc (E := E) (n := a) w₀
  have hnap : ¬ Apart w₀ w₀ := not_apart_self w₀
  have hloc : ∀ k ∈ K, ∀ x, cLoc w₀ (k * x) = cLoc w₀ x := fun k hk x => by
    rw [map_mul, hK.one k hk w₀ hnap, one_mul]
  have hnorm : ∀ J' : Subgroup (GL (Fin a) (w₀.adicCompletion E)),
      K ≤ Subgroup.normalizer ((locU a w₀ ⊓ J'.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) := by
    intro J'
    have hKL : ∀ k ∈ K, ∀ l ∈ locU a w₀ ⊓ J'.comap (cLoc w₀), k * l * k⁻¹ ∈ locU a w₀ ⊓ J'.comap (cLoc w₀) := by
      rintro k hk l ⟨hl1, hl2⟩
      have hl1' := (mem_locU_iff l).1 hl1
      refine ⟨(mem_locU_iff _).2 ⟨mul_mem (mul_mem (hK.fin hk) hl1'.1) (inv_mem (hK.fin hk)), fun u hu => ?_⟩, ?_⟩
      · simp only [map_mul, map_inv, hl1'.2 u hu, mul_one, mul_inv_cancel]
      · show cLoc w₀ (k * l * k⁻¹) ∈ J'
        simp only [map_mul, map_inv, hK.one k hk w₀ hnap, one_mul, inv_one, mul_one]
        exact hl2
    exact fun k hk => Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => hKL k hk l hl, fun hl => by
      have := hKL k⁻¹ (inv_mem hk) _ hl
      simpa [mul_assoc] using this⟩
  have hmem : ∀ (J' : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (c : UA E a),
      c ∈ lev K w₀ J' ↔ ∃ k ∈ K, ∃ x ∈ locU a w₀, cLoc w₀ x ∈ J' ∧ c = k * x := by
    intro J' c
    show c ∈ K ⊔ (locU a w₀ ⊓ J'.comap (cLoc w₀)) ↔ _
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J'), Set.mem_mul]
    constructor
    · rintro ⟨k, hk, x, hx, rfl⟩
      exact ⟨k, hk, x, hx.1, hx.2, rfl⟩
    · rintro ⟨k, hk, x, hx, hxJ, rfl⟩
      exact ⟨k, hk, x, ⟨hx, hxJ⟩, rfl⟩
  have hJmem : ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J := by
    intro c hc
    obtain ⟨k, hk, x, -, hxJ, rfl⟩ := (hmem J c).1 hc
    rwa [hloc k hk]
  have hLc : IsCompact ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) := by
    have : ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) = s '' (J : Set _) := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨cLoc w₀ x, hx2, hs_eq x hx1⟩
      · rintro ⟨h, hh, rfl⟩
        refine ⟨hs_mem h, ?_⟩
        show cLoc w₀ (s h) ∈ J
        rw [hs_loc]
        exact hh
    rw [this]
    exact hJc.image hs_cont
  refine ⟨⟨sup_le hK.fin (fun x hx => ((mem_locU_iff x).1 (Subgroup.mem_inf.1 hx).1).1), ?_, ?_⟩, hmem J, hJmem,
    ?_, fun y => ⟨s y, hs_mem y, hs_loc y⟩, ?_⟩
  · show IsCompact ((K ⊔ (locU a w₀ ⊓ J.comap (cLoc w₀)) : Subgroup (UA E a)) : Set (UA E a))
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J)]
    exact hK.compact.mul hLc
  · obtain ⟨N₀, hN₀o, hN₀1, hN₀⟩ := hK.isOpen
    let k : UA E a → UA E a := fun x => x * (s (cLoc w₀ x))⁻¹
    have hkc : Continuous k := continuous_id.mul ((hs_cont.comp hcont).inv)
    have hs1 : s 1 = 1 := by
      have := hs_eq 1 (one_mem _)
      rwa [map_one] at this
    refine ⟨k ⁻¹' N₀ ∩ cLoc w₀ ⁻¹' (J : Set _), (hN₀o.preimage hkc).inter (hJo.preimage hcont), ⟨?_, ?_⟩, ?_⟩
    · show k 1 ∈ N₀
      have : k 1 = 1 := by simp [k, hs1]
      rw [this]
      exact hN₀1
    · show cLoc w₀ 1 ∈ J
      rw [map_one]
      exact J.one_mem
    · rintro x ⟨⟨hxN, hxJ⟩, hxf⟩
      have hkx : k x ∈ K := by
        refine hN₀ _ hxN ?_ ?_
        · exact mul_mem hxf (inv_mem ((mem_locU_iff _).1 (hs_mem _)).1)
        · exact one_of_cLoc hw _ (by simp only [k, map_mul, map_inv, hs_loc, mul_inv_cancel])
      refine (hmem J x).2 ⟨k x, hkx, s (cLoc w₀ x), hs_mem _, ?_, by simp [k]⟩
      rw [hs_loc]
      exact hxJ
  · intro c hc h1
    obtain ⟨k, hk, x, hx, -, rfl⟩ := (hmem J c).1 hc
    rw [hloc k hk] at h1
    have hx1 : x = 1 := by
      have h2 := hs_eq x hx
      have hs1 : s 1 = 1 := by
        have := hs_eq 1 (one_mem _)
        rwa [map_one] at this
      rw [h1, hs1] at h2
      exact h2.symm
    rw [hx1, mul_one]
    exact hk
  · intro J' c hc hcJ'
    obtain ⟨k, hk, x, hx, -, rfl⟩ := (hmem J c).1 hc
    rw [hloc k hk] at hcJ'
    exact (hmem J' _).2 ⟨k, hk, x, hx, hcJ', rfl⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.locComm_pf :
    UpperTheory.Gal.Gen.LocComm := by
  intro E _ _ _ a w₀ x g hx hg
  obtain ⟨hxf, hxa⟩ := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  have hxi : cInf x = 1 := hxf
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
  · change cInf (x * g) = cInf (g * x)
    rw [map_mul, map_mul, hxi, one_mul, mul_one]
  · change cLoc u (x * g) = cLoc u (g * x)
    rw [map_mul, map_mul]
    by_cases hu : Apart u w₀
    · rw [hxa u hu, one_mul, mul_one]
    · rw [hg u hu, one_mul, mul_one]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.smoothAt_pf :
    UpperTheory.Gal.Gen.SmoothAt := by
  intro E _ _ _ a w₀ hw W f
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let p : GL (Fin a) (w₀.adicCompletion E) → finU (E := E) (n := a) := fun y =>
    ⟨(e.symm y).1, (Subgroup.mem_inf.1 (e.symm y).2).1⟩
  have hp : Continuous p :=
    Continuous.subtype_mk (continuous_subtype_val.comp e.symm.continuous) _
  have hp1 : p 1 = 1 := by
    apply Subtype.ext
    simp [p]
  have hS : IsOpen {k : finU (E := E) (n := a) | algRep W k f = f} := GlobalTheory.DefU.isSmooth_algRep W f
  refine ⟨p ⁻¹' {k : finU (E := E) (n := a) | algRep W k f = f},
    (hS.preimage hp).mem_nhds (by simp [hp1]), fun x hx hxN v g => ?_⟩
  have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
    rw [← he ⟨x, hx⟩]
    exact e.symm_apply_apply _
  have h2 : algRep W (p (cLoc w₀ x)) f = f := hxN
  have h3 : (p (cLoc w₀ x)).1 = x := by
    simp only [p, h1]
  have h4 := congrArg (fun F : algForms W => F.1 v g) h2
  change f.1 v (g * (p (cLoc w₀ x)).1) = f.1 v g at h4
  rwa [h3] at h4
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.neglAt_pf :
    UpperTheory.Gal.Gen.GlobOp → UpperTheory.Gal.Gen.Small → UpperTheory.Gal.Gen.NeglAt := by
  intro hG hS E _ _ _ a K w₀ w hs hap hyp Φ hΦ δ hδ
  obtain ⟨C, hC⟩ := hG E a K w hs hyp
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨p, hp, hp1, hI⟩ := hS a Φ hΦ (δ / (|C| + 1)) (div_pos hδ hC1)
  obtain ⟨h, hloc, hsep, hnorm, hop⟩ := hC p hp
  refine ⟨h, ?_, hsep, ?_, ?_⟩
  · intro g hg
    have hm := (GlobalTheory.Cong.LevelExt.mem_locU_iff g).1 (hloc g hg)
    refine ⟨hm.1, fun u hu => hm.2 u ?_⟩
    have e : u.under (𝓞 (maximalRealSubfield E)) = w₀.under (𝓞 (maximalRealSubfield E)) :=
      Classical.byContradiction hu
    intro e'
    exact hap (e'.symm.trans e)
  · have hI0 : 0 ≤ ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    calc ∑ g ∈ h.support, ‖h g‖ ^ 2
        ≤ C * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 := hnorm
      _ ≤ |C| * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hI0
      _ ≤ |C| * (δ / (|C| + 1)) := mul_le_mul_of_nonneg_left hI (abs_nonneg C)
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ hC1]
          nlinarith [abs_nonneg C]
  · intro U hU hB φ hφ hfix
    have hB' : ¬ GenAt w Φ U := hB
    unfold GenAt at hB'
    push_neg at hB'
    obtain ⟨z, hz, h0⟩ := hB'
    rw [hop U hU z hz φ hφ hfix, hp1 z h0, one_smul]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ratFin_pf :
    UpperTheory.Gal.Gen.RatFin := by
  intro E _ _ _ a
  refine ⟨?_, ?_⟩
  · intro Z hZ
    haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
    set_option synthInstance.maxHeartbeats 200000 in
    have hcl : IsClosed (((ratGL E a).range : Subgroup (GA E a)) : Set (GA E a)) := Subgroup.isClosed_of_discrete
    let K : Set (GA E a) := Subtype.val '' Z
    have hK : IsCompact K := hZ.image continuous_subtype_val
    have hKG : IsCompact (K ∩ ((ratGL E a).range : Set (GA E a))) := hK.inter_right hcl
    let t : Set (ratGL E a).range := {x | (x : GA E a) ∈ K}
    have himg : Subtype.val '' t = K ∩ ((ratGL E a).range : Set (GA E a)) := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
      · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
    have ht : IsCompact t := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
    have hfin : (K ∩ ((ratGL E a).range : Set (GA E a))).Finite := by
      rw [← himg]; exact (ht.finite_of_discrete).image _
    refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨x, ⟨hxZ, hxr⟩, rfl⟩
    exact ⟨⟨x, hxZ, rfl⟩, (Subgroup.mem_subgroupOf).1 hxr⟩
  · intro w γ hγ h1
    obtain ⟨δ, hδ⟩ := (Subgroup.mem_subgroupOf).1 hγ
    have hδ1 : δ = 1 := by
      ext i j
      have h2 := congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.1 i j) h1
      have h3 : (cLoc w γ : GL (Fin a) (w.adicCompletion E)).1 i j = algebraMap E (w.adicCompletion E) (δ.1 i j) := by
        simp [cLoc, ← hδ, pLoc, pFin, ratGL]
        rfl
      have h4 : algebraMap E (w.adicCompletion E) (δ.1 i j) =
          algebraMap E (w.adicCompletion E) ((1 : GL (Fin a) E).1 i j) := by
        rw [← h3]
        refine h2.trans ?_
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      exact (algebraMap E (w.adicCompletion E)).injective h4
    apply Subtype.ext
    rw [← hδ, hδ1, map_one]; rfl
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private theorem sq_sum_of_subsingleton {G : Type} (F : Finset G) (hF : ∀ g ∈ F, ∀ g' ∈ F, g = g') (t : G → ℂ) :
    ‖∑ g ∈ F, t g‖ ^ 2 = ∑ g ∈ F, ‖t g‖ ^ 2 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
  · simp
  · have e : F = {g} := Finset.eq_singleton_iff_unique_mem.2 ⟨hg, fun g' h' => hF _ h' _ hg⟩
    subst e
    simp

private theorem fibre_sum {G Y : Type} [Fintype Y] [DecidableEq Y] (S : Finset G) (π : G → Y)
    (hπ : ∀ g ∈ S, ∀ g' ∈ S, π g = π g' → g = g') (t : G → ℂ) :
    ∑ y, ‖∑ g ∈ S with π g = y, t g‖ ^ 2 = ∑ g ∈ S, ‖t g‖ ^ 2 := by
  refine Eq.trans ?_ (Finset.sum_fiberwise S π fun g => ‖t g‖ ^ 2)
  refine Finset.sum_congr rfl fun y _ => sq_sum_of_subsingleton _ (fun g hg g' hg' => ?_) t
  rw [Finset.mem_filter] at hg hg'
  exact hπ g hg.1 g' hg'.1 (hg.2.trans hg'.2.symm)

private noncomputable def mat {G X : Type} [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) : Matrix (X × Fin d) (X × Fin d) ℂ :=
  fun r s => ∑ g ∈ S with π r.1 g = s.1, t g * m r.1 g r.2 s.2

private theorem mat_mulVec {G X : Type} [Fintype X] [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) (u : X × Fin d → ℂ) (y : X) (i : Fin d) :
    (mat S π t m).mulVec u (y, i) = ∑ g ∈ S, t g * ∑ j, m y g i j * u (π y g, j) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mat, Finset.sum_mul]
  refine Eq.trans ?_ (Finset.sum_fiberwise S (π y) _)
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [(Finset.mem_filter.1 hg).2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

private theorem mat_hs {G X : Type} [Fintype X] [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) (M₀ : ℝ) (hm : ∀ y g i j, ‖m y g i j‖ ≤ M₀)
    (hπ : ∀ y, ∀ g ∈ S, ∀ g' ∈ S, π y g = π y g' → g = g') :
    ∑ r, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ ((d : ℝ) ^ 2 * M₀ ^ 2) * Fintype.card X * ∑ g ∈ S, ‖t g‖ ^ 2 := by
  have hrow : ∀ r : X × Fin d, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ (d : ℝ) * (M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2) := by
    intro r
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hj : ∀ j : Fin d, ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 ≤ M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2 := by
      intro j
      have e := fibre_sum S (π r.1) (hπ r.1) (fun g => t g * m r.1 g r.2 j)
      calc ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 = ∑ g ∈ S, ‖t g * m r.1 g r.2 j‖ ^ 2 := e
        _ ≤ ∑ g ∈ S, M₀ ^ 2 * ‖t g‖ ^ 2 := Finset.sum_le_sum fun g _ => by
            rw [norm_mul, mul_pow, mul_comm]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hm _ _ _ _) 2) (by positivity)
        _ = _ := (Finset.mul_sum _ _ _).symm
    calc ∑ j : Fin d, ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 ≤ ∑ j : Fin d, M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  calc ∑ r, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ ∑ r : X × Fin d, (d : ℝ) * (M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => hrow r
    _ = _ := by
      simp [Fintype.card_prod]
      ring

private theorem sep_eq {G : Type} [Group G] (R N C : Subgroup G) (hN : N.Normal) {z γ γ' x x' c c' : G}
    (hγ : γ ∈ R) (hγ' : γ' ∈ R) (hx : x ∈ N) (hx' : x' ∈ N) (hc : c ∈ C) (hc' : c' ∈ C) :
    ∃ Γ ∈ R, ∃ ξ ∈ N, ∃ k ∈ C, γ' * z * x' * c' = Γ * (γ * z * x * c) * ξ * k :=
  ⟨γ' * γ⁻¹, R.mul_mem hγ' (R.inv_mem hγ), c⁻¹ * (x⁻¹ * x') * c,
    hN.conj_mem' _ (N.mul_mem (N.inv_mem hx) hx') c, c⁻¹ * c', C.mul_mem (C.inv_mem hc) hc', by group⟩

private theorem form_val {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {W : Wt E a} {C : Subgroup (UA E a)}
    {f : algForms W} (hf : f ∈ fixedBy W C) {d : ℕ} (B : Module.Basis (Fin d) ℂ W.Sp) {γ q x c : UA E a}
    (hγ : γ ∈ ratU E a) (hx : x ∈ infU E a) (hc : c ∈ C) (v : W.Sp) :
    f.1 v (γ * q * x * c) = ∑ j, B.repr (W.rep ⟨x, hx⟩ v) j * f.1 (B j) q := by
  have h1 : f.1 v (γ * q * x * c) = f.1 (W.rep ⟨x, hx⟩ v) q := by
    rw [mem_fixedBy.1 hf c hc v, mul_assoc γ q x, (f.2.1 v).left γ hγ, f.2.2 ⟨x, hx⟩ v]
    rfl
  refine h1.trans ?_
  have h2 := congrFun (congrArg f.1 (B.sum_repr (W.rep ⟨x, hx⟩ v))) q
  refine h2.symm.trans ?_

  rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.countCore_pf :
    UpperTheory.Gal.Gen.HS → UpperTheory.Gal.Gen.WBound → UpperTheory.Gal.Gen.CountCore := by
  classical
  intro hHS hWB E _ _ _ a W
  let d := Module.finrank ℂ W.Sp
  let B : Module.Basis (Fin d) ℂ W.Sp := Module.finBasis ℂ W.Sp
  obtain ⟨M₀, hM₀⟩ := hWB E a W d B
  refine ⟨(d : ℝ) ^ 2 * M₀ ^ 2, by positivity, ?_⟩
  intro C X _ p hcov h hsep V hVC hV
  choose γ hγ π ξ hξ c hc hdec using fun (y : X) (g : UA E a) => hcov (p y * g)
  let η : X → UA E a → infU E a := fun y g => ⟨ξ y g, hξ y g⟩
  let m : X → UA E a → Fin d → Fin d → ℂ := fun y g i j => B.repr (W.rep (η y g) (B i)) j
  let ev : V →ₗ[ℂ] (X × Fin d → ℂ) :=
    { toFun := fun f q => f.1.1 (B q.2) (p q.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf0
    have hz : ∀ j y, f.1.1 (B j) (p y) = 0 := fun j y => congrFun hf0 (y, j)
    refine Subtype.ext (Subtype.ext (LinearMap.ext fun v => funext fun g => ?_))
    obtain ⟨γ₀, hγ₀, y, x, hx, c₀, hc₀, rfl⟩ := hcov g
    rw [form_val (hVC f.2) B hγ₀ hx hc₀ v]
    exact Finset.sum_eq_zero fun j _ => by rw [hz, mul_zero]
  have hfix : ∀ f : V, (mat h.support π h m).mulVec (ev f) = ev f := by
    intro f
    funext ⟨y, i⟩
    rw [mat_mulVec]
    have hop := congrFun (hV f.1 f.2 (B i)) (p y)
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul] at hop
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) hop
    rw [hdec y g, form_val (hVC f.2) B (hγ y g) (hξ y g) (hc y g) (B i)]
    rfl
  have hπ : ∀ y, ∀ g ∈ h.support, ∀ g' ∈ h.support, π y g = π y g' → g = g' := by
    intro y g hg g' hg' e
    obtain ⟨Γ, hΓ, ξ', hξ', k, hk, e'⟩ := sep_eq (ratU E a) (infU E a) C inferInstance (z := p (π y g))
      (hγ y g) (hγ y g') (hξ y g) (hξ y g') (hc y g) (hc y g')
    refine hsep y g hg g' hg' Γ hΓ ξ' hξ' k hk ?_
    have e1 := hdec y g'
    rw [← e] at e1
    rw [e1, e', ← hdec y g]
  have hfd : FiniteDimensional ℂ V := FiniteDimensional.of_injective ev hinj
  refine ⟨hfd, ?_⟩
  have h1 := hHS (X × Fin d) (mat h.support π h m) (LinearMap.range ev) (by rintro _ ⟨f, rfl⟩; exact hfix f)
  rw [LinearMap.finrank_range_of_inj hinj] at h1
  exact h1.trans (mat_hs h.support π h m M₀ (fun y g i j => hM₀ (η y g) i j) hπ)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.stepCore_pf :
    UpperTheory.Gal.Gen.AlgC → UpperTheory.Gal.Gen.Codim → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.StepCore := by
  intro hAlg hCod hPF E _ _ _ l _ ι a W C C' hCfin H _ _ hH lam hsurj hC'C hker ℓ hinf hright haut P hfd hcard f hf
  letI : Fintype H := Fintype.ofFinite H
  have hex : ∀ φ : H → ℂ, ∃ F : algForms W, ∀ v g, F.1 v g = φ (ℓ g) * f.1 v g := fun φ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => φ (ℓ g)) (haut φ) (fun g x hx => by simp only [hinf g x hx])
  choose Ψ₀ hΨ₀ using hex
  let Ψ : (H → ℂ) →ₗ[ℂ] algForms W :=
    { toFun := Ψ₀
      map_add' := fun φ ψ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hΨ₀]
        ring
      map_smul' := fun c φ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, hΨ₀, RingHom.id_apply, smul_eq_mul]
        ring }
  have hΨ : ∀ φ v g, (Ψ φ).1 v g = φ (ℓ g) * f.1 v g := hΨ₀
  have hfix : ∀ φ, Ψ φ ∈ fixedBy W C' := fun φ k hk v g => by
    have hkC : k ∈ C := hC'C hk
    have h1 : lam ⟨k, hkC⟩ = 1 := (hker ⟨k, hkC⟩).1 hk
    have h2 : ℓ (g * k) = ℓ g := by
      have := hright g ⟨k, hkC⟩
      rw [h1, mul_one] at this
      exact this
    rw [hΨ, hΨ, h2, hf k hkC v g]
  obtain ⟨h1, -, -, h4, -⟩ := hPF E a W C' P
  have hdim := hCod ℂ (H → ℂ) (algForms W) Ψ (part W C' P) (part W C' fun U => ¬ P U) (fun φ => h1 (hfix φ))
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  rw [Nat.card_eq_fintype_card] at hcard
  have hA : Fintype.card H ≤ 2 * Module.finrank ℂ ((part W C' P).comap Ψ) := by omega
  have hstable : ∀ c ∈ (part W C' P).comap Ψ, ∀ u, (fun h => c (h * u)) ∈ (part W C' P).comap Ψ := by
    intro φ hφ u
    obtain ⟨c, rfl⟩ := hsurj u
    have hnorm : ∀ c' ∈ C', (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C' := by
      intro c' hc'
      have hc'C : c' ∈ C := hC'C hc'
      have hm : (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C := C.mul_mem (C.mul_mem (C.inv_mem c.2) hc'C) c.2
      refine (hker ⟨_, hm⟩).2 ?_
      have e1 : (⟨_, hm⟩ : C) = c⁻¹ * ⟨c', hc'C⟩ * c := Subtype.ext rfl
      rw [e1, map_mul, map_mul, (hker ⟨c', hc'C⟩).1 hc', mul_one, map_inv, inv_mul_cancel]
    have hrep : Ψ (fun h => φ (h * lam c)) = algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ) :=
      Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        have e2 : (algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ)).1 v g = (Ψ φ).1 v (g * c.1) := rfl
        rw [e2, hΨ, hΨ, hright g c, hf c.1 c.2 v g]
    change Ψ _ ∈ part W C' P
    rw [hrep]
    exact h4 ⟨c.1, hCfin c.2⟩ hnorm _ hφ
  obtain ⟨φ, hφ, hnorm⟩ := hAlg l ι H hH _ hstable hA
  exact ⟨Ψ φ, hφ, fun g => 1 - φ (ℓ g), fun g => hnorm (ℓ g), fun v g => by rw [hΨ]; ring⟩
end
