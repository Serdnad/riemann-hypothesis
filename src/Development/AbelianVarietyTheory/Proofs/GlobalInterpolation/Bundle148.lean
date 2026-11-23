module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle106
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle087
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle145
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.MomLat

theorem latticeFactsAll : GlobalTheory.MomT.LatticeFactsAll := by
  intro D X s cc δ B χ cD hX hs hcc hδ hχ a b ha hb
  have hL := GlobalTheory.ThetaMove.LatticeFacts.latAll B hcc hδ
  have hVm := B.vec_mem_ne hcc hδ (delta_ne_zero B) (B.stdOK hcc hδ) χ hχ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hVm a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hVm a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.MomLat
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitarySplit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* finU (E := E) (n := n) :=
  ((((finGL E n).comp (GeneralLinearGroup.map (pFin E))).comp (UA E n).subtype).codRestrict (UA E n)
    fun g => GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)).codRestrict (finU (E := E) (n := n))
    fun _ => pInf_finGL _

def infPart : UA E n →* infU E n :=
  (((infGL E n).comp cInf).codRestrict (UA E n)
    fun g => by
      have h := (UA E n).mul_mem g.2 ((UA E n).inv_mem (finPart g).1.2)
      have e : (finPart g).1.1 = finGL E n (GeneralLinearGroup.map (pFin E) g.1) := rfl
      rw [e] at h
      nth_rewrite 1 [← infGL_mul_finGL g.1] at h
      rw [mul_inv_cancel_right] at h
      exact h).codRestrict (infU E n)
    fun _ => pFin_infGL _

theorem finPart_val (g : UA E n) : (finPart g).1.1 = finGL E n (GeneralLinearGroup.map (pFin E) g.1) := rfl

theorem infPart_val (g : UA E n) : (infPart g).1.1 = infGL E n (GeneralLinearGroup.map (pInf E) g.1) := rfl

theorem continuous_finPart : Continuous (finPart (E := E) (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact GlobalTheory.DefU.ClassFin.continuous_finGL.comp
    ((Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
      continuous_subtype_val)

theorem continuous_infPart : Continuous (infPart (E := E) (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact GlobalTheory.DefU.continuous_infGL.comp GlobalTheory.DefU.continuous_cInf

theorem finPart_mul_infPart (g : UA E n) : g = (finPart g).1 * (infPart g).1 := by
  rw [GlobalTheory.DefU.fin_mul_inf (finPart g).2 (infPart g).2]
  exact Subtype.ext (infGL_mul_finGL g.1).symm

theorem cInf_infPart (g : UA E n) : cInf (infPart g).1 = cInf g := pInf_infGL _

theorem finPart_fin (g : finU (E := E) (n := n)) : finPart g.1 = g :=
  Subtype.ext (Subtype.ext (GlobalTheory.CuspRep.ga_ext ((pInf_finGL _).trans g.2.symm) (pFin_finGL _)))

theorem infPart_inf (k : infU E n) : infPart k.1 = k :=
  Subtype.ext (Subtype.ext (GlobalTheory.CuspRep.ga_ext (pInf_infGL _) ((pFin_infGL _).trans k.2.symm)))

theorem finPart_inf (k : infU E n) : finPart k.1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  have h : GeneralLinearGroup.map (pFin E) k.1.1 = 1 := k.2
  rw [finPart_val, h, map_one]
  rfl

theorem infPart_fin (g : finU (E := E) (n := n)) : infPart g.1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  have h : GeneralLinearGroup.map (pInf E) g.1.1 = 1 := g.2
  rw [infPart_val, h, map_one]
  rfl

theorem dense_rat_inf : Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} := by
  intro k
  rw [← infPart_inf k]
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_infPart
    ⟨k.1, GlobalTheory.WeightRealExt.dense_rat_fin k.1, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, g, hg, rfl⟩, rfl⟩
  refine ⟨γ, hγ, ?_⟩
  have hg' : cInf g = 1 := hg
  rw [cInf_infPart, map_mul, hg', mul_one]

theorem dense_and_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU (E := E) (n := n)) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  intro E _ _ _ n
  refine ⟨GlobalTheory.WeightRealExt.dense_rat_fin, dense_rat_inf, fun k g hg => (GlobalTheory.DefU.fin_mul_inf hg k.2).symm,
    finPart, infPart, continuous_finPart, continuous_infPart, finPart_mul_infPart, fun g k => ⟨?_, ?_⟩⟩
  · rw [map_mul, finPart_fin, finPart_inf, mul_one]
  · rw [map_mul, infPart_fin, infPart_inf, one_mul]

end GlobalTheory.UnitarySplit

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Formalism.L2.Host (HChar atFin upF aboveF IsUnitAt ordF)
open GlobalTheory.CharVal (valuation_conjP conjP_conjP')
open GlobalTheory.NormOneUnit (locK_unr locK_tame exists_of_star_eq under_eq_iff)

namespace GlobalTheory.NormOneProd

variable {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]


omit [StarRing E] in
theorem exists_val_eq {P : HeightOneSpectrum (𝓞 E)}
    (hu : ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) (x : Eˣ) :
    ∃ k : Fˣ, P.valuation E ((x / upF F k : Eˣ) : E) = 1 := by
  obtain ⟨k, hk⟩ := (P.under (𝓞 F)).valuation_surjective F (P.valuation E (x : E))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at hk
    exact x.ne_zero hk
  refine ⟨Units.mk0 k hk0, ?_⟩
  have hy' : ((x / upF F (Units.mk0 k hk0) : Eˣ) : E) = x / algebraMap F E k := Units.val_div_eq_div_val _ _
  rw [hy', map_div₀, GlobalTheory.MuConj.valuation_up P hu, hk, div_self (by simp)]

theorem split_unit (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P ≠ conjPrime₂ P) {y y' : Eˣ} (hy : (y' : E) = star (y : E))
    (h2 : (conjPrime₂ P).valuation E (y : E) = 1) : χ.locK P y' * χ.locK (conjPrime₂ P) y = 1 := by
  classical
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hP
  have he1 : P.valuation E (e : E) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 he
  have hy0 : P.valuation E (y : E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ he1 (Units.mk0 _ hy0)⁻¹
  have hn' : P.valuation E ((e : E) ^ n * y) < 1 := by
    rw [map_mul, map_pow]
    rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
    rwa [← lt_div_iff₀ (zero_lt_iff.2 hy0), one_div]
  have hm : e ^ n - 1 ∈ (conjPrime₂ P).asIdeal := by
    refine Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one e n) ?_
    have : e - 1 = -e' := by rw [← hee]; ring
    rw [this]
    exact neg_mem he'
  obtain ⟨k, hk⟩ := exists_of_star_eq hF hr hc (x := (e : E) ^ n * y + star ((e : E) ^ n * y : E))
    (by rw [star_add, star_star, add_comm])
  have v1 : (conjPrime₂ P).valuation E (algebraMap F E k - y) < 1 := by
    have e1 : algebraMap F E k - y = ((e ^ n - 1 : 𝓞 E) : E) * y + star ((e : E) ^ n * y : E) := by
      rw [hk]; push_cast; ring
    rw [e1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, h2, mul_one]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm
    · rw [valuation_conjP, star_star]
      exact hn'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_sub, Valuation.map_neg, h2] at v1
    exact lt_irrefl _ v1
  have a1 : χ.locK (conjPrime₂ P) (upF F (Units.mk0 k hk0)) = χ.locK (conjPrime₂ P) y := locK_tame (ht _) h2 v1
  have a2 : χ.locK P (upF F (Units.mk0 k hk0)) = χ.locK P y' := by
    refine locK_tame (ht _) (hy ▸ (valuation_conjP P _).symm.trans h2) ?_
    rw [valuation_conjP, star_sub, hF, ← hy] at v1
    exact v1
  have hab : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext Q
    rw [GlobalTheory.Mem.ReadTwist.mem_above, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff hF hr hc P Q
  have h := hχ.1 (P.under (𝓞 F)) (Units.mk0 k hk0)
  rwa [HChar.resFin_apply, hab, Finset.prod_pair hP, a1, a2] at h


open Classical in
theorem place_prod (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a)
    (hu : ∀ P : HeightOneSpectrum (𝓞 E),
      ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2)
    {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) (hun : ∀ P, conjPrime₂ P = P → χ.UnrAt P)
    {x z : Eˣ} (hxz : (x : E) = z * star (x : E)) (P : HeightOneSpectrum (𝓞 E)) :
    ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q x = χ.locK P z := by
  obtain ⟨k, hk⟩ := exists_val_eq (hu (conjPrime₂ P)) x
  set y : Eˣ := x / upF F k with hy
  have hy' : (y : E) = x / algebraMap F E k := Units.val_div_eq_div_val _ _
  have hyz : (y : E) = z * star (y : E) := by
    rw [hy', star_div₀, hF, ← mul_div_assoc, ← hxz]
  have h := hχ.1 (P.under (𝓞 F)) k
  rw [HChar.resFin_apply] at h
  have e1 : ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q x = ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q y := by
    simp only [hy, map_div, Finset.prod_div_distrib, h, div_one]
  have hab : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext Q
    rw [GlobalTheory.Mem.ReadTwist.mem_above, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff hF hr hc P Q
  rw [e1, hab]
  by_cases hP : P = conjPrime₂ P
  · have h1 : P.valuation E (y : E) = 1 := hP ▸ hk
    have h2 : P.valuation E (z : E) = 1 := by
      have h3 := congrArg (P.valuation E) hyz
      rw [map_mul, ← valuation_conjP, hk, h1, mul_one] at h3
      exact h3.symm
    rw [← hP, Finset.pair_eq_singleton, Finset.prod_singleton, locK_unr (hun P hP.symm) h1, locK_unr (hun P hP.symm) h2]
  · have hs0 : star (y : E) ≠ 0 := star_ne_zero.2 y.ne_zero
    have h3 := split_unit hF hr hc hχ ht hP (y' := Units.mk0 _ hs0) rfl hk
    have e2 : y = z * Units.mk0 _ hs0 := Units.ext hyz
    rw [Finset.prod_pair hP, congrArg (χ.locK P) e2, map_mul, mul_assoc, h3, mul_one]

theorem inf_mul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (rep : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E)) (V : Finset (HeightOneSpectrum (𝓞 F))) (x z : Eˣ), (∀ y : F, star (algebraMap F E y) = algebraMap F E y) → Module.finrank F E = 2 → (∃ a : E, star a ≠ a) → (∀ P : HeightOneSpectrum (𝓞 E), ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) → χ.TrivOn F → (∀ P, χ.TameAt P) → (∀ P, conjPrime₂ P = P → χ.UnrAt P) → (∀ v, (rep v).under (𝓞 F) = v) → (x : E) = z * star (x : E) → (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ V → χ.UnrAt P ∧ P.valuation E (x : E) = 1) → χ.inf x * ∏ v ∈ V, χ.locK (rep v) z = 1 := by
  intro F E _ _ _ _ _ _ χ rep V x z hF hr hc hu hχ ht hun hrep hxz hV
  classical
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), P ∈ V.biUnion (aboveF (L := E) F) ↔ P.under (𝓞 F) ∈ V := fun P => by
    simp only [Finset.mem_biUnion, GlobalTheory.Mem.ReadTwist.mem_above, exists_eq_right']
  have h := GlobalTheory.HeckeProduct.productRule χ (V.biUnion (aboveF (L := E) F)) (fun P hP => (hV P fun e => hP ((hm P).2 e)).1) x
  have hfp : (∏ᶠ (P : HeightOneSpectrum (𝓞 E)) (_ : P ∉ V.biUnion (aboveF (L := E) F)), χ.val P ^ ordF P x) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun P => ?_
    by_cases hP : P ∈ V.biUnion (aboveF (L := E) F)
    · rw [finprod_eq_if, if_neg (not_not.2 hP)]
    rw [finprod_eq_if, if_pos hP, ordF, (hV P fun e => hP ((hm P).2 e)).2, WithZero.log_one, neg_zero, zpow_zero]
  have hpl : ∀ v ∈ V, ∏ Q ∈ aboveF (L := E) F v, χ.locK Q x = χ.locK (rep v) z := fun v _ => by
    have := place_prod hF hr hc hu hχ ht hun hxz (rep v)
    rwa [hrep] at this
  rw [hfp, mul_one, Finset.prod_biUnion, Finset.prod_congr rfl hpl] at h
  · exact h
  · intro v _ w _ hvw
    exact Finset.disjoint_left.2 fun P h1 h2 =>
      hvw ((GlobalTheory.Mem.ReadTwist.mem_above.1 h1).symm.trans (GlobalTheory.Mem.ReadTwist.mem_above.1 h2))

end GlobalTheory.NormOneProd
end
end
