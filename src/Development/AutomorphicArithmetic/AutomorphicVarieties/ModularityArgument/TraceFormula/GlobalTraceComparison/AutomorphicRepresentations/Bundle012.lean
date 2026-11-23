module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
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
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem logAbs_det_centre (τ : ℝ) :
    logAbs (splitCentre E n τ).val.det = Module.finrank ℚ E * (n * τ) := by
  have h := congrArg (fun g : GA E n => logAbs g.val.det) (Dcy.splitCentre_mul_tor (E := E) (n := n) τ (fun _ => 0))
  simp only [Dcy.logAbs_det_mul', Dcy.logAbs_det_tor] at h
  simpa using h

private theorem ldet_ac (hn : 1 ≤ n) (t : ℝ) : ldet (ac E n t) = t := by
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  change logAbs (splitCentre E n (t / (n * Module.finrank ℚ E))).val.det = t
  rw [logAbs_det_centre]
  field_simp

private theorem logAbs_det_inv (g : GA E n) : logAbs (g⁻¹ : GA E n).val.det = -logAbs g.val.det := by
  have h := Dcy.logAbs_det_mul' g g⁻¹
  have h1 := Dcy.logAbs_ratGL' (E := E) (n := n) 1
  rw [map_one] at h1
  rw [mul_inv_cancel, h1] at h
  linarith

private theorem logAbs_det_theta (g : GA E n) : logAbs (thetaA E n g).val.det = -logAbs g.val.det := by
  have h : (thetaA E n g).val.det = conjAd E (g⁻¹ : GA E n).val.det := by
    change (((g⁻¹ : GA E n).val.map (conjAd E))ᵀ).det = _
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (conjAd E) _).symm
  rw [h, GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj D1.conjPlaces, logAbs_det_inv]

end SlopeTestRemainingChoices

theorem basic_pf : Basic := by
  intro E _ _ _ n hn
  refine ⟨ldet_ac hn, fun x y => Dcy.logAbs_det_mul' x.1 y.1, fun t x => ?_, fun s t => ?_, ?_, ?_, fun x => ?_, fun x => ?_,
    fun x y => ?_, ?_, continuous_ldet, ?_⟩
  · refine Prod.ext ?_ ?_
    · exact CuspidalL2GL.splitCentre_comm _ _
    · change 1 * x.2 = x.2 * 1
      rw [one_mul, mul_one]
  · refine Prod.ext ?_ (mul_one _).symm
    change splitCentre E n ((s + t) / _) = splitCentre E n (s / _) * splitCentre E n (t / _)
    rw [add_div, CuspidalL2GL.splitCentre_add]
  · refine Prod.ext ?_ rfl
    change splitCentre E n (0 / _) = 1
    rw [zero_div, CuspidalL2GL.splitCentre_zero]
  · exact (GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp (continuous_id.div_const _)).prodMk continuous_const
  · exact logAbs_det_theta x.1
  · exact Prod.ext ((thetaBasic_holds E n).2.1 x.1) ((thetaBasic_holds E 0).2.1 x.2)
  · exact Prod.ext (map_mul (thetaA E n) x.1 y.1) (map_mul (thetaA E 0) x.2 y.2)
  · rintro ⟨_, γ, rfl⟩
    refine ⟨Dcy.logAbs_ratGL' γ.1, ⟨(thetaE E n γ.1, thetaE E 0 γ.2), ?_⟩⟩
    exact Prod.ext ((thetaBasic_holds E n).2.2 γ.1).symm ((thetaBasic_holds E 0).2.2 γ.2).symm
  · exact (((thetaBasic_holds E n).1.comp continuous_fst).prodMk ((thetaBasic_holds E 0).1.comp continuous_snd))

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private lemma shiftInt (D : Dom E n 0) (a : H E n 0) (F : H E n 0 → ℂ) :
    ∫ y, F (a * y) ∂D.μ = ∫ y, F y ∂D.μ := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI := D.haar.1
  exact integral_mul_left_eq_self F a

private lemma ldet_shift (a : GA E n) (h : logAbs a.val.det = 0) (y : H E n 0) :
    ldet (((a, 1) : H E n 0) * y) = ldet y := by
  simp only [ldet, Prod.fst_mul, DiscreteGroups.T1.G.Dcy.logAbs_det_mul', h, zero_add]

private lemma cv_shift (D : Dom E n 0) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (g a : GA E n)
    (h : logAbs a.val.det = 0) :
    cvF D.μ φ u f (g * a) = ∫ y, φ ((a⁻¹, 1) * y) * u (ldet y) * f (g * y.1) ∂D.μ := by
  rw [← shiftInt D ((a, 1) : H E n 0) (fun y => φ ((a⁻¹, 1) * y) * u (ldet y) * f (g * y.1))]
  unfold cvF
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e : ((a⁻¹, 1) : H E n 0) * (((a, 1) : H E n 0) * y) = y := by
    rw [← mul_assoc]; simp
  simp only [e, ldet_shift a h, Prod.fst_mul, mul_assoc]

private lemma term_integrable (D : Dom E n 0) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (g a : GA E n)
    (hφ : IsTestH φ) (hu : Continuous u) (hf : Continuous f) :
    Integrable (fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1)) D.μ := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI := D.haar.2.2.2
  haveI : IsFiniteMeasureOnCompacts D.μ :=
    ⟨fun _ h => h.measure_lt_top_of_nhdsWithin fun x _ => D.μ.finiteAt_nhdsWithin x _⟩
  have c1 : Continuous fun y : H E n 0 => φ ((a, 1) * y) := hφ.1.comp (continuous_const.mul continuous_id)
  have s1 : HasCompactSupport fun y : H E n 0 => φ ((a, 1) * y) :=
    hφ.2.comp_homeomorph (Homeomorph.mulLeft ((a, 1) : H E n 0))
  have s3 : HasCompactSupport fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1) :=
    (s1.mul_right (f' := fun y : H E n 0 => u (ldet y))).mul_right (f' := fun y : H E n 0 => f (g * y.1))
  have c3 : Continuous fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1) :=
    (c1.mul (hu.comp DiscreteGroups.T1.G.continuous_ldet)).mul (hf.comp (continuous_const.mul continuous_fst))
  exact c3.integrable_of_hasCompactSupport s3

theorem cvType_pf : DetZero → EvalBasis → CvType := by
  intro hdz hev E _ _ _ n D K W φ u f hK hW hφ hL hu hf
  refine ⟨fun k hk g => ?_, fun g => ?_⟩
  · rw [cv_shift D φ u f g _ ((hdz E n).2 K hK k hk)]
    unfold cvF
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have := hL.1 k⁻¹ (K.inv_mem hk) y
    simp only [map_inv] at this
    simp only [this]
  · obtain ⟨d, x, w, hw, hs⟩ := hev (Kinf E n) (Kinf E n → ℂ) (fun x => LinearMap.proj x)
      (fun v hv => funext hv) W hW
    set c : Fin d → ℂ := fun b =>
      ∫ y, φ (((kI E n (x b))⁻¹, 1) * y) * u (ldet y) * f (g * y.1) ∂D.μ with hc
    have key : (fun k : Kinf E n => cvF D.μ φ u f (g * kI E n k)) = ∑ b, c b • w b := by
      funext k
      rw [cv_shift D φ u f g _ ((hdz E n).1 k)]
      have e : ∀ y : H E n 0, φ (((kI E n k)⁻¹, 1) * y) * u (ldet y) * f (g * y.1) =
          ∑ b, w b k * (φ (((kI E n (x b))⁻¹, 1) * y) * u (ldet y) * f (g * y.1)) := by
        intro y
        have := congrFun (hs _ (hL.2 y)) k
        simp only [LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [this, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      simp only [e]
      rw [integral_finsetSum _ fun b _ => (term_integrable D φ u f g _ hφ hu hf).const_mul _]
      simp only [integral_const_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [key]
    exact Submodule.sum_mem _ fun b _ => W.smul_mem _ (hw b)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem zero_of_powers_compact {G : Type*} [Monoid G] [TopologicalSpace G] (f : G → ℝ) (hf : Continuous f)
    (hm : ∀ x y, f (x * y) = f x + f y) (S : Set G) (hS : IsCompact S) (k : G) (hk : ∀ m : ℕ, k ^ m ∈ S) : f k = 0 := by
  obtain ⟨C, hC⟩ := (hS.image hf).isBounded.exists_norm_le
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ m : ℕ, f (k ^ m) = m * f k := by
    intro m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih]; push_cast; ring
  by_contra hne
  have hpos : 0 < |f k| := abs_pos.2 hne
  obtain ⟨m, hmC⟩ := exists_nat_gt (C / |f k|)
  have hb := hC _ ⟨k ^ m, hk m, rfl⟩
  rw [hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at hb
  rw [div_lt_iff₀ hpos] at hmC
  linarith

private theorem continuous_kI (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (kI E n) := by
  have hu : Continuous (Unitary.toUnits : Kinf E n → _) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  exact GlobalTheory.CuspQuot.continuous_infGL.comp hu

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.detZero_pf :
    DetZero := by
  intro E _ _ _ n
  have hc := DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)
  have hm := DiscreteGroups.T1.G.Dcy.logAbs_det_mul' (E := E) (n := n)
  refine ⟨fun k => ?_, fun K hK k hk => ?_⟩
  · haveI : CompactSpace (Kinf E n) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
    exact zero_of_powers_compact _ hc hm (Set.range (kI E n)) (isCompact_range (continuous_kI E n)) _
      fun m => ⟨k ^ m, map_pow _ _ _⟩
  · exact zero_of_powers_compact _ hc hm (finGL E n '' (K : Set _))
      (hK.image GlobalTheory.BCT.GlobLev.continuous_finGL_ad) _ fun m => ⟨k ^ m, K.pow_mem hk m, map_pow _ _ _⟩
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 (K2)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Generic

variable {G H : Type} [Group G] [Group H] [Subsingleton H]

private theorem hint_prod (K : Subgroup G) (K₂ : Subgroup H) (u : G × H → ℂ)
    (hu : ∀ k ∈ K.prod K₂, ∀ x, u (x * k) = u x) : hint (K.prod K₂) u = hint K fun g => u (g, 1) := by
  have hv : ∀ k ∈ K, ∀ x, (fun g => u (g, 1)) (x * k) = (fun g => u (g, 1)) x := by
    intro k hk x
    have := hu (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩) (x, 1)
    simpa using this
  rw [UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.hintSph (G × H) (K.prod K₂) u hu, UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.hintSph G K _ hv]
  have hout : ∀ y : G × H, u ((y : (G × H) ⧸ K.prod K₂).out) = u y := by
    intro y
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.prod K₂) y
    rw [hh]
    exact hu h h.2 y
  symm
  refine finsum_eq_of_bijective (fun q : G ⧸ K => (((q.out, 1) : G × H) : (G × H) ⧸ K.prod K₂)) ⟨?_, ?_⟩ ?_
  · intro p q h
    have h' := QuotientGroup.eq.1 h
    have h1 : p.out⁻¹ * q.out ∈ K := by simpa using (Subgroup.mem_prod.1 h').1
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 h1
  · intro q'
    obtain ⟨⟨x, h⟩, rfl⟩ := QuotientGroup.mk_surjective q'
    refine ⟨(x : G ⧸ K), QuotientGroup.eq.2 ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
    refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
    · simp [hk]
    · rw [Subsingleton.elim (((((x : G ⧸ K).out, 1) : G × H)⁻¹ * (x, h)).2) 1]
      exact K₂.one_mem
  · intro q
    exact (hout _).symm

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem tj_zero (w : Pl E) (j : ℕ) (y : GLw 0 w) : Tj ℂ 0 (Ov E w) (unif w) j y = 1 := by
  unfold Tj
  refine Set.indicator_of_mem ?_ _
  exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, Subsingleton.elim _ _⟩

private def toFirst (n : ℕ) (p : Fin (n + 1) × Fin (0 + 1)) : Ex (Fin (n + 1)) := .gen p.1

private theorem fn2_zero_apply_one_eq_fn1_bind (w : Pl E) (e : Ex (Fin (n + 1) × Fin (0 + 1))) (g : GLw n w) :
    fn2 n 0 w e (g, 1) = fn1 n w (e.bind (toFirst n)) g := by
  induction e generalizing g with
  | one =>
    show (K2 n 0 w : Set (GLw n w × GLw 0 w)).indicator (1 : GLw n w × GLw 0 w → ℂ) (g, 1) =
      (KGL w (n := n) : Set (GLw n w)).indicator (1 : GLw n w → ℂ) g
    by_cases h : g ∈ KGL w (n := n)
    · rw [Set.indicator_of_mem (show (g, (1 : GLw 0 w)) ∈ (K2 n 0 w : Set _) from
        Subgroup.mem_prod.2 ⟨h, Subgroup.one_mem _⟩), Set.indicator_of_mem (show g ∈ (KGL w (n := n) : Set _) from h)]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h (Subgroup.mem_prod.1 h').1),
        Set.indicator_of_notMem (show g ∉ (KGL w (n := n) : Set _) from h)]
  | gen p =>
    show Tj ℂ n (Ov E w) (unif w) p.1 g * Tj ℂ 0 (Ov E w) (unif w) p.2 1 = Tj ℂ n (Ov E w) (unif w) p.1 g
    rw [tj_zero, mul_one]
  | smul c a ih =>
    show c * fn2 n 0 w a (g, 1) = c * fn1 n w (a.bind (toFirst n)) g
    rw [ih]
  | add a b iha ihb =>
    show fn2 n 0 w a (g, 1) + fn2 n 0 w b (g, 1) = fn1 n w (a.bind (toFirst n)) g + fn1 n w (b.bind (toFirst n)) g
    rw [iha, ihb]
  | mul a b iha ihb =>
    show hint (K2 n 0 w) (fun z => fn2 n 0 w a z * fn2 n 0 w b (z⁻¹ * (g, 1))) =
      hint (KGL w (n := n)) fun z => fn1 n w (a.bind (toFirst n)) z * fn1 n w (b.bind (toFirst n)) (z⁻¹ * g)
    have hA := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E n 0 w a
    have hB := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E n 0 w b
    rw [hint_prod (KGL w (n := n)) (KGL w (n := 0)) _ fun c hc z => ?_]
    · congr 1
      funext z
      rw [iha, ← ihb]
      congr 2
      simp
    · show fn2 n 0 w a (z * c) * fn2 n 0 w b ((z * c)⁻¹ * (g, 1)) = fn2 n 0 w a z * fn2 n 0 w b (z⁻¹ * (g, 1))
      rw [(hA.2 c hc z).2, _root_.mul_inv_rev, mul_assoc, (hB.2 c⁻¹ ((K2 n 0 w).inv_mem hc) _).1]

private theorem ev_bind (w : Pl E) (B : Multiset ℂˣ) (e : Ex (Fin (n + 1) × Fin (0 + 1))) :
    ev2 n 0 w e B 0 = ev1 n w (e.bind (toFirst n)) B := by
  have h0 : ∀ p : Fin (n + 1) × Fin (0 + 1), satEig (qV E w) 0 0 p.2 = 1 := by
    intro p
    have h : ((p.2 : Fin (0 + 1)) : ℕ) = 0 := by
      have := p.2.2
      omega
    rw [h]
    exact GlobalTheory.LFun.ConjPlace.satEig_zero _ _ _
  induction e with
  | one => rfl
  | gen p =>
    show satEig (qV E w) n B p.1 * satEig (qV E w) 0 0 p.2 = satEig (qV E w) n B p.1
    rw [h0, mul_one]
  | smul c a ih =>
    show c * ev2 n 0 w a B 0 = c * ev1 n w (a.bind (toFirst n)) B
    rw [ih]
  | add a b iha ihb =>
    show ev2 n 0 w a B 0 + ev2 n 0 w b B 0 = ev1 n w (a.bind (toFirst n)) B + ev1 n w (b.bind (toFirst n)) B
    rw [iha, ihb]
  | mul a b iha ihb =>
    show ev2 n 0 w a B 0 * ev2 n 0 w b B 0 = ev1 n w (a.bind (toFirst n)) B * ev1 n w (b.bind (toFirst n)) B
    rw [iha, ihb]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.ex2Act_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.ExAct → Ex2Act := by
  intro hEx E _ _ _ n w e
  have hf : (fun g => fn2 n 0 w e (g, 1)) = fn1 n w (e.bind (toFirst n)) := funext fun g => fn2_zero_apply_one_eq_fn1_bind w e g
  obtain ⟨h1, h2⟩ := hEx E n w (e.bind (toFirst n))
  rw [hf]
  refine ⟨h1, fun V _ _ ρ x B hx => ?_⟩
  rw [ev_bind]
  exact h2 V ρ x B hx
end
end
