module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle586
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle596
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle381
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle554
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle574
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (d : B.A), B.I = Ideal.span {d} → IsUnit (B.D.δ d) := by
  first | exact @GlobalTheory.BSP.isUnit_δ_of_I_eq_span | exact GlobalTheory.BSP.isUnit_δ_of_I_eq_span | (intros; apply GlobalTheory.BSP.isUnit_δ_of_I_eq_span <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prism_hom_map_ideal_eq : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I := by
  first | exact @GlobalTheory.Prism.Rigid.map_I_eq | exact GlobalTheory.Prism.Rigid.map_I_eq | (intros; apply GlobalTheory.Prism.Rigid.map_I_eq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem rootT_mul' {l : ℕ} [Fact l.Prime] (a b : Per.Fl l) (n : ℕ) :
    GlobalTheory.MemLoc.rootT (a * b) n = GlobalTheory.MemLoc.rootT a n * GlobalTheory.MemLoc.rootT b n := by
  unfold GlobalTheory.MemLoc.rootT
  rw [← map_mul]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem rootT_succ_pow' {l : ℕ} [Fact l.Prime] (a : Per.Fl l) (n : ℕ) :
    GlobalTheory.MemLoc.rootT a (n + 1) ^ l = GlobalTheory.MemLoc.rootT a n := by
  unfold GlobalTheory.MemLoc.rootT
  rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem galois_moves_flat_by_unit_root : ∀ (l : ℕ) [Fact l.Prime], (∀ (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x) → ∀ (K : FinExt l) (bk : BK K) (e : OCb l), e.untilt = 1 → ∃ g : ↥(GK K), Per.σF (g : GQ l) bk.flat = e * bk.flat := by
  intro l _ hroots K bk e he
  obtain ⟨hπ, hπu⟩ := GlobalTheory.BSP.BK.prime_unif l K bk
  obtain ⟨halg, hfix⟩ := GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  choose y hy using halg
  have hc : ∀ n : ℕ, ∃ c : Om l, (c : ℂ_[l]) = ((GlobalTheory.MemLoc.rootT e n : OC l) : ℂ_[l]) := by
    intro n
    refine hroots _ (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) ?_
    have h := congrArg (fun x : OC l => (x : ℂ_[l])) (GlobalTheory.MemLoc.rootT_pow_eq_untilt e n)
    simpa [he] using h
  choose c hc using hc
  have hcoe : ∀ x : Om l, (x : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x := fun _ => rfl
  have hinj : Function.Injective (fun x : Om l => (x : ℂ_[l])) := (algebraMap (Om l) ℂ_[l]).injective
  have hy0 : y 0 = (((bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) : ↥(OL K)) : ↥K.1) : Om l) := by
    apply hinj
    beta_reduce
    rw [← hy 0, ← coe_intToOC, hπu]
    rfl
  have hc0 : c 0 = 1 := by
    apply hinj
    beta_reduce
    rw [hc 0, hcoe, map_one]
    show ((PreTilt.untilt e : OC l) : ℂ_[l]) = 1
    rw [he]
    rfl
  have hys : ∀ n, y (n + 1) ^ l = y n := by
    intro n
    apply hinj
    show ((y (n + 1) ^ l : Om l) : ℂ_[l]) = (y n : ℂ_[l])
    rw [hcoe, map_pow, ← hcoe, ← hy, ← hy, ← SubmonoidClass.coe_pow, rootT_succ_pow']
  have hcs : ∀ n, c (n + 1) ^ l = c n := by
    intro n
    apply hinj
    show ((c (n + 1) ^ l : Om l) : ℂ_[l]) = (c n : ℂ_[l])
    rw [hcoe, map_pow, ← hcoe, hc, hc, ← SubmonoidClass.coe_pow, rootT_succ_pow']
  obtain ⟨g, hg⟩ := GlobalTheory.galois_transitive_on_root_systems_of_prime l K _ hπ y (fun n => c n * y n) hy0
    (by rw [hc0, one_mul, hy0]) hys (fun n => by rw [mul_pow, hcs, hys])
  refine ⟨g, hfix _ _ fun n => ?_⟩
  apply Subtype.ext
  refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_
  rw [hy n, GlobalTheory.RingBasics.σC_coe, hg n, rootT_mul']
  rw [MulMemClass.coe_mul, hcoe, map_mul, ← hcoe, ← hcoe, hc n, hy n]

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_pow_of_ne_zero_untilt (l : ℕ) [Fact l.Prime] (y : Formalism.Per.OC l) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ (l : Formalism.Per.OC l) ^ n := by
  have hy' : (y : ℂ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
  have hpos : 0 < ‖(y : ℂ_[l])‖ := norm_pos_iff.2 hy'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (GlobalTheory.RingBasics.norm_p_lt (p := l))
  refine ⟨n, ⟨(l : ℂ_[l]) ^ n / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, norm_pow, div_le_one hpos]
    exact hn.le
  · push_cast
    exact (mul_div_cancel₀ _ hy').symm

theorem constantCoeff_natCast_untilt (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] :
    WittVector.constantCoeff ((l : ℕ) : WittVector l O) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem exists_untilt_map : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∃ θ' : OC l →+* (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}), (∀ a : Ainf l, θ' (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ a)) ∧ Function.Injective θ' ∧ IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∧ ∀ a : WittVector l O, ((l : ℕ) : WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∣ Ideal.Quotient.mk _ a → ψ bk.flat ^ bk.Ep.natDegree ∣ a.coeff 0 := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc
  obtain ⟨w, hw, hE⟩ := GlobalTheory.T.breuilKisin_eisenstein_image_teichmuller_pow l K bk O ψ hu
  obtain ⟨hp, hl⟩ := GlobalTheory.T.teichmullerDistinguished_span_isPrime_and_not_mem l O _ h0 hu hc _ w _ bk.deg_pos hw hE
  have hdom : IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) :=
    Ideal.Quotient.isDomain _
  have hker : RingHom.ker (Per.θ l) ≤ RingHom.ker ((Ideal.Quotient.mk
      (Ideal.span {WittVector.map ψ (bk.ev bk.E)})).comp (WittVector.map ψ)) := by
    rw [← bk.span_ev, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  refine ⟨(Per.θ l).liftOfSurjective (theta_onto (l := l)) ⟨_, hker⟩, fun a => ?_, ?_, hdom, ?_⟩
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  · rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hne
    obtain ⟨n, z, hz⟩ := dvd_pow_of_ne_zero_untilt l y hne
    have h := congrArg ((Per.θ l).liftOfSurjective (theta_onto (l := l)) ⟨_, hker⟩) hz
    rw [map_mul, hy, zero_mul, map_pow, map_natCast] at h
    have h2 := eq_zero_of_pow_eq_zero h
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem] at h2
    exact hl h2
  · rintro a ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, hc⟩ := hb
    have h := congrArg WittVector.constantCoeff hc
    rw [hE, map_mul, map_add (f := _), map_mul, map_sub, map_mul, constantCoeff_natCast_untilt, zero_mul, zero_mul,
      add_zero, sub_zero, map_pow, WittVector.constantCoeff_apply (WittVector.teichmuller _ _),
      WittVector.teichmuller_coeff_zero] at h
    exact ⟨_, h.symm.trans (mul_comm _ _)⟩

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ApproxRoot

theorem mul_eval_derivative_scaleRoots {R : Type} [CommRing R] (p : Polynomial R) (s r : R) :
    s * (Polynomial.derivative (p.scaleRoots s)).eval (s * r) =
      s ^ p.natDegree * (Polynomial.derivative p).eval r := by
  have h : (p.scaleRoots s).comp (Polynomial.C s * Polynomial.X) = Polynomial.C s ^ p.natDegree * p := by
    have := Polynomial.scaleRoots_eval₂_mul (p := p) Polynomial.C Polynomial.X s
    rwa [Polynomial.eval₂_C_X] at this
  rw [← map_pow] at h
  have h2 := congrArg (fun t => (Polynomial.derivative t).eval r) h
  simp only [Polynomial.derivative_C_mul] at h2
  simpa [Polynomial.derivative_comp, Polynomial.eval_comp] using h2

theorem sub_mem_pow {R : Type} [CommRing R] (I : Ideal R) (P : Polynomial R) (s r x : R) (n : ℕ) (hs : IsUnit s)
    (hr : P.eval r = 0) (hd : IsUnit ((Polynomial.derivative P).eval r))
    (hx : (P.scaleRoots s).eval x ∈ I ^ n) (hxy : x - s * r ∈ I) : x - s * r ∈ I ^ n := by
  have hy : (P.scaleRoots s).eval (s * r) ∈ I ^ n := by
    rw [Polynomial.scaleRoots_eval_mul, hr, mul_zero]
    exact zero_mem _
  have h := GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow R I (P.scaleRoots s) (s * r) x s (s ^ P.natDegree * (Polynomial.derivative P).eval r) n
    hy hx (by rw [← neg_sub]; exact neg_mem hxy)
    (by rw [mul_eval_derivative_scaleRoots, sub_self]; exact zero_mem _)
  rw [Ideal.unit_mul_mem_iff_mem _ (((hs.pow _).mul hd).pow n)] at h
  rw [← neg_sub]
  exact neg_mem h

end GlobalTheory.BSP.ApproxRoot


open GlobalTheory.BSP.ApproxRoot in
theorem GlobalTheory.BSP.approxRoot_sub_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → aDp l (bk.ev q) - (l : Per.BdRp l) ^ m * C.o (((bk.str.symm (Ideal.Quotient.mk _ X) : ↥(OL K)) : ↥K.1) : Om l) ∈ Per.FilP l n := by
  intro l _ K bk C n m q hq hroot
  obtain ⟨hfil, -⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (bk.ev bk.E) bk.span_ev
  obtain ⟨-, hker, -, hth, -⟩ := thetaD_props l
  let e : bk.S →+* Per.BdRp l := (aDp l).comp bk.ev
  let f : Wq l bk.a →+* Per.BdRp l := (aDp l).comp (wA l bk.a)
  let g : bk.S →+* Per.BdRp l := C.o.comp ((K.1.val : ↥K.1 →+* Om l).comp (((OL K).val : ↥(OL K) →+* ↥K.1).comp
    (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk _))))
  have hg : ∀ s, g s = C.o (((bk.str.symm (Ideal.Quotient.mk _ s) : ↥(OL K)) : ↥K.1) : Om l) := fun _ => rfl
  have hθ : ∀ s : bk.S, ((Per.θ l (bk.ev s) : OC l) : ℂ_[l]) =
      ((((bk.str.symm (Ideal.Quotient.mk _ s) : ↥(OL K)) : ↥K.1) : Om l) : ℂ_[l]) := fun s => by
    rw [bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s)) s (bk.str.apply_symm_apply _).symm, coe_intToOC]
  have hef : e.comp PowerSeries.C = f := RingHom.ext fun w => congrArg (aDp l) (bk.ev_C w)
  have hgf : g.comp PowerSeries.C = f := RingHom.ext fun w =>
    GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w _ (by rw [← bk.ev_C]; exact hθ _)
  have hgE : g bk.E = 0 := by
    rw [hg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    simp
  have hθeg : ∀ s, Per.θD l (e s) = Per.θD l (g s) := fun s => by
    rw [hg, C.o_sec.th]
    exact (hth _).trans (hθ s)
  have hl : IsUnit ((l : Per.BdRp l) ^ m) := (isUnit_l_BdRp l).pow m
  have hr : (bk.Ep.map f).eval (g X) = 0 := by
    rw [Polynomial.eval_map, ← hgf, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X_eq_coe]
    exact hgE
  have hd : IsUnit ((Polynomial.derivative (bk.Ep.map f)).eval (g X)) := by
    obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
    have h := congrArg (fun t => (Polynomial.map f t).eval (g X)) hab
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.eval_add, Polynomial.eval_mul, hr, mul_zero,
      zero_add, Polynomial.map_C, Polynomial.eval_C, map_pow f, map_natCast f] at h
    rw [Polynomial.derivative_map]
    exact isUnit_of_mul_isUnit_right (h ▸ (isUnit_l_BdRp l).pow c)
  haveI : Nontrivial (Per.BdRp l) := (Per.θD l).domain_nontrivial
  have hx : ((bk.Ep.map f).scaleRoots ((l : Per.BdRp l) ^ m)).eval (e q) ∈ Ideal.span {e bk.E} ^ n := by
    have h1 : (bk.Ep.map f).scaleRoots ((l : Per.BdRp l) ^ m) =
        (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)).map f := by
      rw [Polynomial.map_scaleRoots _ _ _ (by rw [bk.monic.leadingCoeff, map_one]; exact one_ne_zero), map_pow,
        map_natCast]
    rw [h1, Polynomial.eval_map, ← hef, ← Polynomial.hom_eval₂, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← map_pow]
    exact map_dvd e hroot
  have hxy : e q - (l : Per.BdRp l) ^ m * g X ∈ Ideal.span {e bk.E} := by
    have h1 : e q - (l : Per.BdRp l) ^ m * g X ∈ Per.FilP l 1 := by
      rw [← hker, map_sub, hθeg, ← map_sub]
      obtain ⟨t, ht⟩ := hq
      have h2 := congrArg g ht
      rw [map_sub, map_mul, map_pow, map_natCast, map_mul, hgE, zero_mul] at h2
      rw [h2, map_zero]
    rwa [hfil, pow_one] at h1
  have h := sub_mem_pow _ _ _ _ _ n hl hr hd hx hxy
  rw [Ideal.span_singleton_pow] at h
  rw [hfil]
  exact h
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem disc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ →
    ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → Function.Injective R := by
  intro l _ K bk ρ ρ' h0 hle h1 R hR
  have hρ0 : 0 < ρ := h0.trans_le hle
  obtain ⟨a, ha1, ha2, ha3, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 h1
  obtain ⟨a', ha1', ha2', -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ' h0 (hle.trans_lt h1)
  obtain ⟨-, -, hdense, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ
  have htors : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    rw [nsmul_eq_mul] at hz
    exact ((isUnit_l_disc l (0 : Wq l bk.a) 1).mul_right_eq_zero).1 hz
  have hbound : ∀ (σ : ℝ≥0), 0 < σ → ∀ (b : bk.DS σ →+ Disc l (0 : Wq l bk.a) 1) (n : ℕ),
      (∀ y, ‖b y‖ * (σ : ℝ) ^ n ≤ ‖y‖) → ∀ y, ‖b y‖ ≤ ((σ : ℝ) ^ n)⁻¹ * ‖y‖ := by
    intro σ hσ b n hb y
    have hp : (0 : ℝ) < (σ : ℝ) ^ n := pow_pos (by exact_mod_cast hσ) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb y
  have hcoef : ∀ n y, a' n (R y) = a n y := by
    intro n
    have e := hdense (Disc l (0 : Wq l bk.a) 1) htors ((a' n).comp R.toAddMonoidHom) (a n)
      (AddMonoidHomClass.continuous_of_bound _ (((ρ' : ℝ) ^ n)⁻¹) fun y =>
        (hbound ρ' h0 (a' n) n (ha2' n) (R y)).trans
          (mul_le_mul_of_nonneg_left (hR.norm_le y) (inv_nonneg.2 (by positivity))))
      (AddMonoidHomClass.continuous_of_bound _ (((ρ : ℝ) ^ n)⁻¹) (hbound ρ hρ0 (a n) n (ha2 n)))
      (fun x => by
        change a' n (R (toDisc l (X : bk.S) ρ x)) = a n (toDisc l (X : bk.S) ρ x)
        rw [hR.ext x, RingHom.id_apply, ha1', ha1])
    intro y
    exact DFunLike.congr_fun e y
  refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
  have h := ha3 y 0 le_rfl fun n => by rw [← hcoef n y, hy, map_zero, norm_zero, zero_mul]
  exact norm_le_zero_iff.1 h

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.breuilKisin_mem_ideal_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ), ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S, (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  first | exact @GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem | exact GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem | (intros; apply GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.closedDisc_topologicalBasis_expansion : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) s j → ∀ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), ((∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖)) → ∀ y, Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0) ∧ HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y := by
  first | exact @GlobalTheory.BSP.DiscExpand.disc_expand | exact GlobalTheory.BSP.DiscExpand.disc_expand | (intros; apply GlobalTheory.BSP.DiscExpand.disc_expand <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.approx_bdRPlus_fil_matrix_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n d : ℕ) (X Z : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * X i j ∈ Per.FilP l n) → (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * Z i j ∈ Per.FilP l n) → ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * (X * Z) i j ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.use₁₀) | (exact GlobalTheory.use₁₀) | (intros; apply GlobalTheory.use₁₀  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d k : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * ε g)) → Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) → (∀ g : ↥(GK K), (ε g).map (fun a => algebraMap (Ainf l) (Per.Acris l) (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q) → ∃ U : Matrix (Fin d) (Fin d) (Per.Bcris l), IsUnit U ∧ ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := by
  first | (exact @GlobalTheory.BcrisInv.invariant_unit) | (exact GlobalTheory.BcrisInv.invariant_unit) | (intros; apply GlobalTheory.BcrisInv.invariant_unit  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  first | (exact @GlobalTheory.FlatKummer.exists_kummer_flat) | (exact GlobalTheory.FlatKummer.exists_kummer_flat) | (intros; apply GlobalTheory.FlatKummer.exists_kummer_flat  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  first | exact @GlobalTheory.AcrisPow.main | exact GlobalTheory.AcrisPow.main | (intros; apply GlobalTheory.AcrisPow.main <;> assumption)
end
