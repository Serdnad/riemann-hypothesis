module

import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle041
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import ReciprocityTheory.DualLattices.Bundle016

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host nonZeroDivisors

namespace GlobalTheory.HeckeProduct

section Comp
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion L)

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion L)

theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) w = x
  convert Pi.mulSingle_eq_same w (x : w.Completion)

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) u = 1
  convert Pi.mulSingle_eq_of_ne h (x : w.Completion)

end Comp

section Parts
variable (F : Type) [Field F] [NumberField F]

def infPart : Ideles F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finPart : Ideles F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem infDiag_parts (k : Fˣ) : infPart F (infDiag k) = infPart F (diagUnits F k) ∧ finPart F (infDiag k) = 1 := by
  classical
  constructor
  · apply Units.ext
    funext w
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    have e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) :
        InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) :
          (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w := Finset.prod_apply _ _ _
    rw [e, Finset.prod_eq_single w]
    · exact infIdele_fst_self F w _
    · intro u _ hu
      exact infIdele_fst_ne F u w (Ne.symm hu) _
    · simp
  · rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => Units.ext rfl

end Parts

section Product

variable {F : Type} [Field F] [NumberField F]


open Classical in
def cut (a : FiniteAdeleRing (𝓞 F) F) (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', if_false]
    exact one_mem _⟩

theorem tendsto_cut (a : FiniteAdeleRing (𝓞 F) F) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  apply GlobalTheory.Mem.Chr.CharModel.tendsto_cut <;> assumption

theorem prod_local (k : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F) =
      (((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).1, cut ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).2 T) := by
  classical
  refine Prod.ext ?_ ?_
  · change ((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _
    have e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1 := Finset.prod_eq_one (fun v _ => Units.ext rfl)
    rw [map_mul, map_prod, (infDiag_parts k).1, e, mul_one]
    rfl
  · change ((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _
    rw [map_mul, (infDiag_parts k).2, one_mul]
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)
    | insert u T hu ih =>
      rw [Finset.prod_insert hu, map_mul, Units.val_mul, ih]
      refine Subtype.ext (funext fun v => ?_)
      change ((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) =
        if v ∈ insert u T then _ else 1
      by_cases h : v = u
      · subst h
        rw [localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]; rfl
      · rw [localIdele_snd_ne F u v h, one_mul]; simp [h]

theorem tendsto_prod_local (k : Fˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
      Filter.atTop (nhds (diagUnits F k)) := by
  apply GlobalTheory.Mem.Chr.CharModel.tendsto_prod_local <;> assumption

theorem locK_unr (χ : HChar F) {v : HeightOneSpectrum (𝓞 F)} (h : χ.UnrAt v) (k : Fˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  apply GlobalTheory.Mem.Chr.CharModel.locK_unr <;> assumption

theorem finite_ordF (k : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v k ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))
  refine h.subset fun v hv h0 => hv ?_
  have hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
  rw [GlobalTheory.Idele.ord_vw, hk] at h0
  exact h0

theorem productRule (χ : HChar F) : χ.ProductRule := by
  apply GlobalTheory.Mem.Chr.CharModel.productRule <;> assumption

end Product

theorem hchar_productRule : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), χ.ProductRule :=
  fun _ _ _ χ => productRule χ

end GlobalTheory.HeckeProduct
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.ThetaD

section general
variable {R : Type} [CommRing R] (I : Ideal R)

theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl

theorem isUnit_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by
  apply GlobalTheory.ValCompletion.isUnit_evalₐ <;> assumption

theorem isUnit_of_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ I y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _

end general

variable (l : ℕ) [Fact l.Prime]

theorem frob_surj : Function.Surjective (frobenius (ModP (Per.OC l) l) l) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl
  have hb1 : b ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC]
    have := (GlobalTheory.RingBasics.mem_OC _).1 a.2
    rw [← hb, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this
  refine ⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  exact congrArg _ (Subtype.ext hb)

theorem θ_surj : Function.Surjective (Per.θ l) := surjective_fontaineTheta (frob_surj l)

theorem fontaineTheta_algebraMap₂ (a : Per.Ainf l) : Per.θP l (algebraMap _ _ a) = (Per.θ l a : ℂ_[l]) :=
  GlobalTheory.RingIface.fontaineTheta_algebraMap l a

theorem fontaineTheta_eq_zero (a : Per.AinfP l) : Per.θP l a = 0 ↔ a ∈ Per.kerP l := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one])⟩
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) a
  have hs := IsLocalization.map_units (Per.AinfP l) s
  have h1 := congrArg (Per.θP l) hx
  rw [map_mul, h, zero_mul, fontaineTheta_algebraMap₂] at h1
  have h2 : Per.θ l x = 0 := Subtype.ext h1.symm
  have h3 := GlobalTheory.RingIface.alg_mem_kerP l h2
  have h4 : a * algebraMap (Per.Ainf l) (Per.AinfP l) (s : Per.Ainf l) ∈ Per.kerP l := by
    rw [hx]; exact h3
  exact (Ideal.mul_unit_mem_iff_mem _ hs).1 h4

theorem fontaineTheta_surjective' : Function.Surjective (Per.θP l) := by
  intro c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l]) ^ n * c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : ℂ_[l])) GlobalTheory.RingBasics.norm_p_lt).mul_const ‖c‖
    rw [zero_mul] at h
    obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds one_pos)).exists
    exact ⟨n, by rwa [norm_mul, norm_pow]⟩
  obtain ⟨a, ha⟩ := θ_surj l ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩
  obtain ⟨u, hu⟩ := ((GlobalTheory.RingBasics.isUnit_l l).pow n).exists_left_inv
  refine ⟨u * algebraMap _ _ a, ?_⟩
  have h := congrArg (Per.θP l) hu
  rw [map_mul, map_pow, map_natCast, map_one] at h
  rw [map_mul, fontaineTheta_algebraMap₂, ha]
  change _ * (_ * c) = c
  rw [← mul_assoc, h, one_mul]

theorem θP_σ (g : Per.Gq l) (a : Per.AinfP l) :
    Per.θP l (Per.extP (Per.σA g) a) = Per.σC g (Per.θP l a) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := (Per.θP l).comp (Per.extP (Per.σA g))) (k := (Per.σC g).comp (Per.θP l))
    (RingHom.ext fun y => ?_)) a
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, fontaineTheta_algebraMap₂, GlobalTheory.RingBasics.θ_σA]
  exact GlobalTheory.RingIface.sigO_coe l g _

theorem θD_of_ev (y : Per.BdRp l) (a : Per.AinfP l) (h : Ideal.Quotient.mk _ a = Per.ev l 1 y) :
    Per.θD l y = Per.θP l a := by
  have h1 : y - algebraMap (Per.AinfP l) (Per.BdRp l) a ∈ Per.FilP l 1 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, GlobalTheory.RingIface.ev_alg, h, sub_self]
  have h2 := GlobalTheory.RingIface.thetaD_of_mem_FilP l h1
  rwa [map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero] at h2

theorem θD_alg (a : Per.AinfP l) : Per.θD l (algebraMap _ _ a) = Per.θP l a :=
  GlobalTheory.RingIface.thetaD_alg l a

end GlobalTheory.MemLoc.ThetaD


open GlobalTheory.MemLoc.ThetaD in
theorem GlobalTheory.MemLoc.thetaD_props : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θD l) ∧ (∀ y : Per.BdRp l, Per.θD l y = 0 ↔ y ∈ Per.FilP l 1) ∧ (∀ y : Per.BdRp l, Per.θD l y ≠ 0 → IsUnit y) ∧ (∀ a : Per.Ainf l, Per.θD l (aDp l a) = (Per.θ l a : ℂ_[l])) ∧ ∀ (g : Per.Gq l) (y : Per.BdRp l), Per.θD l (Per.σDp g y) = Per.σC g (Per.θD l y) := by
  intro l _
  refine ⟨fun c => ?_, fun y => ?_, fun y hy => ?_, fun a => ?_, fun g y => ?_⟩
  · obtain ⟨a, rfl⟩ := fontaineTheta_surjective' l c
    exact ⟨_, θD_alg l a⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha, fontaineTheta_eq_zero, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← ha,
      Ideal.Quotient.eq_zero_iff_mem, pow_one]
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha] at hy
    obtain ⟨b, hb⟩ := fontaineTheta_surjective' l (Per.θP l a)⁻¹
    have h1 : a * b - 1 ∈ Per.kerP l ^ 1 := by
      rw [pow_one, ← fontaineTheta_eq_zero, map_sub, map_mul, hb, map_one, mul_inv_cancel₀ hy, sub_self]
    have hu : IsUnit (Per.ev l 1 y) := by
      rw [← ha]
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ b) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)), Ideal.Quotient.eq]
      exact h1
    obtain ⟨e, -, he⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
    rw [← he] at hu
    have h2 := (isUnit_of_evalₐ (Per.kerP l) (e y) hu).map e.symm
    rwa [RingEquiv.symm_apply_apply] at h2
  · exact (θD_alg l _).trans (fontaineTheta_algebraMap₂ l a)
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha, ← θP_σ]
    exact θD_of_ev l _ _ (GlobalTheory.RingIface.ev_sigDp l g 1 y a ha.symm).symm
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.XiHaus
variable {l : ℕ} [Fact l.Prime]

theorem isDomain_Fl : IsDomain (Per.Fl l) :=
  PreTilt.isDomain ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l) l

theorem coeff_pow_pow (x : Per.Fl l) (k : ℕ) :
    PreTilt.coeff k (x ^ l ^ k) = PreTilt.coeff 0 x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, map_pow, PreTilt.coeff_pow_p, ih]

theorem xi_coeff_zero (e : Per.Fl l) :
    (xi e).coeff 0 = ∑ i ∈ Finset.range l, ((frobeniusEquiv (Per.Fl l) l).symm e) ^ i := by

  rw [← WittVector.constantCoeff_apply, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem root_pow (e : Per.Fl l) : ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = e := by
  simp

theorem xi_coeff_zero_ne {e : Per.Fl l} (he : IsEps e) : (xi e).coeff 0 ≠ 0 := by
  intro h
  have h1 := geom_sum_mul ((frobeniusEquiv (Per.Fl l) l).symm e) l
  rw [← xi_coeff_zero, h, zero_mul, root_pow, eq_comm, sub_eq_zero] at h1
  exact he.2 (by rw [h1, map_one, map_one])

theorem eq_zero_of_dvd {e : Per.Fl l} (he : IsEps e) (b : Per.Fl l)
    (hb : ∀ n : ℕ, ((xi e).coeff 0) ^ n ∣ b) : b = 0 := by
  set u := (frobeniusEquiv (Per.Fl l) l).symm e with hu
  have hy : (u - 1) ∣ (xi e).coeff 0 := by
    rw [xi_coeff_zero, ← hu]
    have : ∑ i ∈ Finset.range l, u ^ i = ∑ i ∈ Finset.range l, (u ^ i - 1 ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow u 1 i
  have h0 : PreTilt.coeff 0 ((u - 1) ^ l) = 0 := by
    rw [sub_pow_char, hu, root_pow, one_pow, map_sub, ← PreTilt.mk_untilt_eq_coeff_zero, he.1,
      map_one, map_one, sub_self]
  refine Perfection.ext fun k => ?_
  obtain ⟨c, hc⟩ := (pow_dvd_pow_of_dvd hy (l * l ^ k)).trans (hb _)
  change PreTilt.coeff k b = PreTilt.coeff k 0
  rw [hc, map_mul, pow_mul, coeff_pow_pow, h0, zero_mul, map_zero]

theorem xi_sat {e : Per.Fl l} (he : IsEps e) (n : ℕ) (a : Per.Ainf l)
    (h : xi e ^ n ∣ (l : Per.Ainf l) * a) : xi e ^ n ∣ a := by
  have := isDomain_Fl (l := l)
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg WittVector.constantCoeff hc
  rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_pow,
    WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at h1
  have h2 : c.coeff 0 = 0 :=
    (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (xi_coeff_zero_ne he))
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero c).2 h2)
  refine ⟨d, mul_left_cancel₀ (WittVector.p_nonzero l (Per.Fl l)) ?_⟩
  rw [hc]; ring

end GlobalTheory.MemLoc.XiHaus

namespace GlobalTheory.MemLoc

open XiHaus in
theorem eq_zero_of_forall_xi_pow_dvd (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : IsEps e)
    (a : Per.Ainf l) (ha : ∀ n : ℕ, xi e ^ n ∣ a) : a = 0 := by
  have key : ∀ (k : ℕ) (a : Per.Ainf l), (∀ n : ℕ, xi e ^ n ∣ a) → (l : Per.Ainf l) ^ k ∣ a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ha
      have h0 : a.coeff 0 = 0 := eq_zero_of_dvd he _ fun n => by
        have := map_dvd WittVector.constantCoeff (ha n)
        rwa [map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at this
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).2 h0)
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih d fun n => xi_sat he n d (ha n))
  refine IsHausdorff.haus (I := Ideal.span {(l : Per.Ainf l)}) inferInstance a fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact key k a ha
end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem core_isEps : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsEps C.ε := by
  intro l _ C
  refine ⟨?_, ?_⟩
  · have h := C.ε_root 0
    rw [C.ζ_zero, map_one] at h
    exact Subtype.ext h
  · intro h1
    have h := C.ε_root 1
    have h2 : rootT C.ε 1 = 1 := h1
    rw [h2] at h
    apply C.ζ_one
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h]
    rfl

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem IsEps.isPrimitiveRoot_untilt {l : ℕ} [hl : Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    IsPrimitiveRoot ((frobeniusEquiv (Per.Fl l) l).symm e).untilt l := by
  have hp : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt ^ l = 1 := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p, h.1]
  have ho := orderOf_eq_prime hp h.2
  have := IsPrimitiveRoot.orderOf ((frobeniusEquiv (Per.Fl l) l).symm e).untilt
  rwa [ho] at this

theorem ker_theta_eq_span_xi {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    RingHom.ker (Per.θ l) = Ideal.span {xi e} := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -⟩ :=
    ReciprocityTheory.PGsh.a0 l ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l)
  exact ((hX e (PadicComplexInt.integers l) h.isPrimitiveRoot_untilt).2.2.2 pf hpf).1

theorem theta_eq_zero_iff_xi_dvd (l : ℕ) [Fact l.Prime] :
    ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  intro e h a
  rw [← RingHom.mem_ker, ker_theta_eq_span_xi h, Ideal.mem_span_singleton]

end GlobalTheory.MemLoc
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

theorem _root_.GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∃ N : ℕ, ∀ f, Sm ρ f → ∃ C : ℝ, ∀ g, ‖Ω g f‖ ≤ C * (1 + ∑ i, ∑ j, ‖m g i j‖) ^ N) ∧ ∀ (γ : ℝ → G) (X : Matrix ι ι ℂ), γ 0 = 1 → (∀ i j, HasDerivAt (fun t => m (γ t) i j) (X i j) 0) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q → ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t => Ω (γ t) f) (quad ρ c p q f + lam • f) 0 := by
  first | exact @GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv | exact GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv | (intros; apply GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv <;> assumption)
end
