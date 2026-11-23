module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle147
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle099
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle126
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle132
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle048
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle092
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle148
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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

@[expose] public section

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslateLaw

variable {q : ℕ} [Fact q.Prime]

theorem inOK_natMul {d : ℕ} (s : ℕ) {v : ℂ} (h : InOK d v) : InOK d ((s : ℂ) * v) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨s * a, s * b, by push_cast; ring⟩

theorem cmLatticeCommutatorPairing_natMul_right (d s : ℕ) (x y : ℂ) : kap1 d x ((s : ℂ) * y) = kap1 d x y ^ s := by
  unfold kap1
  rw [← Complex.exp_nat_mul]
  congr 1
  have : h1 d x ((s : ℂ) * y) = ((s : ℝ) : ℂ) * h1 d x y := by
    simp only [h1, map_mul, map_natCast, Complex.ofReal_natCast]; ring
  rw [this, Complex.im_ofReal_mul]
  push_cast
  ring

theorem norm_natCast_eq_one {s : ℕ} (h : Nat.Coprime s q) : ‖(s : ℤ_[q])‖ = 1 := by
  rw [PadicInt.norm_natCast_eq_one_iff]
  exact h.symm

theorem zc_natCast (s : ℕ) : zc (s : ℤ_[q]) = (s : ℂ_[q]) := by
  simp [zc]

theorem hasSubst_mulS (a : ℤ_[q]) : HasSubst (mulS a : ℂ_[q]⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' ((MulSeries.mulS_laws q).1 a).2.1

theorem subst_mulS_cancel {a : ℤ_[q]} (ha : ‖a‖ = 1) {f g : ℂ_[q]⟦X⟧}
    (h : f.subst (mulS a : ℂ_[q]⟦X⟧) = g.subst (mulS a : ℂ_[q]⟦X⟧)) : f = g := by
  obtain ⟨u, rfl⟩ := PadicInt.isUnit_iff.mpr ha
  have key : ∀ f : ℂ_[q]⟦X⟧, PowerSeries.subst (mulS ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℂ_[q]⟦X⟧)
      (show ℂ_[q]⟦X⟧ from f.subst (mulS (u : ℤ_[q]) : ℂ_[q]⟦X⟧)) = f := by
    intro f
    dsimp only
    rw [subst_comp_subst_apply (hasSubst_mulS _) (hasSubst_mulS _), (MulSeries.mulS_laws q).2.1,
      Units.mul_inv, (MulSeries.mulS_laws q).2.2.1]
    rw [← map_algebraMap_eq_subst_X]
    simp
  have h1 := key f
  have h2 := key g
  dsimp only at h1 h2
  rw [← h1, h, h2]

theorem main : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good M.ι d n s y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ hat M.ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) (U1 d t θ)) := by
  intro d q hq M ω θ hd hd16 hsp hOK hM hθ hgood t y n s hs ht hy
  obtain ⟨v, hv, hvn, hyv⟩ := hy
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      exact absurd ((Nat.coprime_zero_left q).mp hs) hq.out.one_lt.ne'
    · exact h
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsn : ‖(s : ℤ_[q])‖ = 1 := norm_natCast_eq_one hs
  have hιs : M.ι (s : ℂ) = zc (s : ℤ_[q]) := by rw [zc_natCast, map_natCast]
  set y' : ℂ := v / (q : ℂ) ^ n with hy'
  have hyy : y = (s : ℂ) * y' := by rw [hyv, hy']; ring
  have hg' : Good M.ι d n 1 y' := ⟨v, hv, hvn, by rw [hy']; simp⟩
  have hg : Good M.ι d n 1 y := by
    refine ⟨(s : ℂ) * v, inOK_natMul s hv, ?_, by rw [hyv]; simp⟩
    rw [map_mul, map_mul, map_natCast, hιs, norm_mul, (MulSeries.mulS_laws q).2.2.2.2.2, hsn, one_mul]
    exact hvn
  obtain ⟨hζ, hAt⟩ := hgood n y hg
  obtain ⟨hζ', hAt'⟩ := hgood n y' hg'
  refine ⟨hζ, ?_⟩
  have hζζ : M.ι (kap1 d 1 y) = M.ι (kap1 d 1 y') ^ s := by rw [hyy, cmLatticeCommutatorPairing_natMul_right, map_pow]
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hM.2.1
  obtain ⟨hring, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) hℓ
  obtain ⟨-, -, hdiff, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos
  have hθd : Differentiable ℂ θ := hθ.1
  have hθ0 : θ 0 ≠ 0 := by rw [hθ.2.1]; exact one_ne_zero
  have hUd : Differentiable ℂ (U1 d t θ) := (hdiff t θ hθd).1
  have hWUd : Differentiable ℂ (W1 d y (U1 d t θ)) := (hdiff y _ hUd).2
  have hWd : Differentiable ℂ (W1 d y θ) := (hdiff y _ hθd).2
  set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf
  have hfa : AnalyticAt ℂ f 0 := (hUd.analyticAt 0).div (hθd.analyticAt 0) hθ0
  obtain ⟨hEll, hφa, -, -, hφb⟩ := GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hOK hM hθ t s hs0 hs ht
  have hscale : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → hat M.ι (C ω * logS) (fun z => G ((s : ℂ) * z)) =
      (hat M.ι (C ω * logS) G).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧) :=
    fun G hG => (hat_multiplicative_chart q M.ι ω G hG).2.2.1 _ _ hιs
  have hφf : hat M.ι (C ω * logS) (fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)) =
      (hat M.ι (C ω * logS) f).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧) := hscale f hfa
  have hfb : Bdd (hat M.ι (C ω * logS) f) := by
    obtain ⟨B, hB⟩ := hφb
    rw [hφf] at hB
    exact ⟨B, ((MulSeries.mulS_laws q).2.2.2.1 _ _ B hsn).mp hB⟩
  have hθb : Bdd (hat M.ι (C ω * logS) θ) := ⟨1, GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd16 hsp hOK hM hθ⟩
  obtain ⟨ψ, hψa, hψ, hψh⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω _ y' _ hM hAt' hEll hφa hφb
  rw [hφf] at hψh
  have hsc := ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 _ n s (s : ℤ_[q]) _ hζ' (by
    rw [sub_self, norm_zero]; positivity) hfb).2
  rw [hsc, ← hζζ] at hψh

  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), θ ((s : ℂ) * z + y) ≠ 0 := by
    have hA : AnalyticOnNhd ℂ (fun z : ℂ => θ ((s : ℂ) * z + y)) Set.univ :=
      fun z _ => (hθd.comp (hlin.add_const y)).analyticAt z
    rcases (hA 0 trivial).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) h
        (Set.mem_univ (-y / (s : ℂ)))
      apply hθ0
      have e : (s : ℂ) * (-y / (s : ℂ)) + y = 0 := by field_simp; ring
      simpa [e] using this
    · exact h
  have hWs : AnalyticAt ℂ (fun z => W1 d y θ ((s : ℂ) * z)) 0 := (hWd.comp hlin).analyticAt 0
  have hWUs : AnalyticAt ℂ (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) 0 := (hWUd.comp hlin).analyticAt 0
  have hprod : hat M.ι (C ω * logS) (fun z => ψ z * W1 d y θ ((s : ℂ) * z)) =
      hat M.ι (C ω * logS) (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) := by
    refine (hring _ _ (hψa.mul hWs) hWUs).2.2.1 ?_
    filter_upwards [hψ, hne] with z h1z h2z
    have e : (s : ℂ) * (z + y') = (s : ℂ) * z + y := by rw [hyy]; ring
    change ψ z * W1 d y θ ((s : ℂ) * z) = _
    rw [h1z, e]
    simp only [W1]
    generalize U1 d t θ = G
    simp only [U1]
    field_simp
  rw [(hring _ _ hψa hWs).2.1, hψh, hscale _ (hWd.analyticAt 0), hscale _ (hWUd.analyticAt 0),
    ← subst_mul (hasSubst_mulS _)] at hprod
  rw [← subst_mulS_cancel hsn hprod, GlobalTheory.T.cmLatticeWeylOperator_eq_theta_rootOfUnity_shift d q M ω θ hd hd16 hsp hOK hM hθ hgood n y hg,
    ← ((Shift.shift_laws q _ hAt.2.1).2.1 _ _ hfb hθb).2, ← (hring _ _ hfa (hθd.analyticAt 0)).2.1]
  congr 1
  refine (hring _ _ (hfa.mul (hθd.analyticAt 0)) (hUd.analyticAt 0)).2.2.1 ?_
  have : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 := hθd.continuous.continuousAt.eventually_ne hθ0
  filter_upwards [nhdsWithin_le_nhds this] with z hz
  change U1 d t θ z / θ z * θ z = _
  field_simp

end GlobalTheory.MomOne.TranslateLaw
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Transfer

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer GlobalTheory.PowGerm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem dLin_id : dLin (pt R (n := 1) d 0) = 1 := by
  classical
  ext i j
  simp only [dLin, pt, coeff_X, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg]
    intro e
    exact h (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero e)).symm

theorem law_eq {B B' : FB R d O} {ε : PS R 2 d} (h : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε) :
    B.G.F = B'.G.F := funext fun i => ((Related.refl B).law i).trans (h.law i).symm

theorem act_eq {B B' : FB R d O} {ε : PS R 2 d} (h : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε) :
    B.A.act = B'.A.act := funext fun a => ((Related.refl B).act a).trans (h.act a).symm

theorem const_diagSer {B B' : FB R d O} {φ φi : Pt R 1 d} {ε : PS R 2 d} (h : Related B B' φ φi ε) (w0 : O) :
    constantCoeff (diagSer B' w0 ε) = 1 := by
  have h1 := congrArg constantCoeff h.ax1
  rw [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), map_one] at h1
  unfold diagSer
  rw [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (B'.A.const w0) (gp_pt 0))), h1]

theorem exists_inv_pow {σ : Type} (s : MvPowerSeries σ R) (hs : constantCoeff s = 1) (q : ℕ) :
    ∃ un : MvPowerSeries σ R, constantCoeff un = 1 ∧ un * s ^ q = 1 := by
  have hu : IsUnit (s ^ q) := (MvPowerSeries.isUnit_iff_constantCoeff.2 (hs ▸ isUnit_one)).pow q
  obtain ⟨un, hun⟩ := hu.exists_left_inv
  refine ⟨un, ?_, hun⟩
  have := congrArg constantCoeff hun
  rwa [map_mul, map_pow, hs, one_pow, mul_one, map_one] at this

theorem const_gauge {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d}
    (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have h1 := congrArg constantCoeff hh.ax1
  rwa [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), map_zero] at h1

theorem exists_gauge {B B' : FB R d O} {ε : PS R 2 d} (hr : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε)
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {R' : Type} [CommRing R'] [Algebra R' k] (B₂ : FB R' d O)
    (hF : B'.FK k = B₂.FK k) (hA : ∀ a, B'.actK k a = B₂.actK k a)
    (hG : ∀ h, B'.IsCanonGauge k h ↔ B₂.IsCanonGauge k h) (h₀ : PS k 2 d) (hh : B.IsCanonGauge k h₀) :
    ∃ h' : PS k 2 d, B₂.IsCanonGauge k h' ∧ ∀ (w0 : O) (m : ℕ) (f f' : PS k 1 d),
      f' * MvPowerSeries.map (algebraMap R k) (diagSer B' w0 ε) ^ m = f →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (P : MvPolynomial Λ k),
        B₂.nabVal k h' w0 m f' u P = B.nabVal k h₀ w0 m f u P := by
  obtain ⟨h', hh', hv⟩ := GlobalTheory.JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.2.2.2.1 R d O B B' _ _ ε hr k h₀ hh
  refine ⟨h', (hG h').1 hh', fun w0 m f f' hf Λ _ u P => ?_⟩
  have e : (fun i => FB.toK k (pt R (n := 1) d 0 i)) = pt k (n := 1) d 0 := by
    funext i
    simp [pt]
  have h1 := hv w0 m f f' (by rw [e, gt_ev_pt_self]; exact hf) Λ u P
  rw [dLin_id, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [Matrix.one_mulVec] at h1
  rw [← h1]
  unfold FB.nabVal FB.hL
  rw [hF, hA]

theorem eig_map {k : Type} [CommRing k] [Algebra R k] (B : FB R d O) (a : O) (u : Fin d → R) (s : R)
    (h : (dAct R B a).mulVec u = s • u) :
    (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k s • fun i => algebraMap R k (u i) := by
  funext i
  have h1 := congrArg (algebraMap R k) (congrFun h i)
  simpa [Matrix.mulVec, dotProduct, dAct, FB.actK, coeff_map] using h1

theorem value_eq [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] {B B' : FB R d O} {ε : PS R 2 d}
    (hr : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε)
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {R' : Type} [CommRing R'] [Algebra R' k] (B₂ : FB R' d O)
    (hF : B'.FK k = B₂.FK k) (hA : ∀ a, B'.actK k a = B₂.actK k a)
    (hG : ∀ h, B'.IsCanonGauge k h ↔ B₂.IsCanonGauge k h) (h₀ h : PS k 2 d) (hh₀ : B.IsCanonGauge k h₀)
    (hh : B₂.IsCanonGauge k h) {T : Type} [Fintype T] (r : T → ℕ) (cc : T → T) (σ : T → O →+* k)
    (hcc : ∀ τ, cc (cc τ) = τ) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) (u : (Σ τ : T, Fin (r τ)) → Fin d → k)
    (hu : ∀ l a, (dAct k B₂ a).mulVec (u l) = σ l.1 a • u l) {n : ℕ}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : ∀ (τ : T) (i : Fin (r τ)) (i' : Fin (r (cc τ))), ∑ b : Fin n,
      MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
        (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0)
    (w0 : O) (q : ℕ) (f f' : Fin n → PS k 1 d)
    (hf : ∀ b, f' b * MvPowerSeries.map (algebraMap R k) (diagSer B' w0 ε) ^ q = f b)
    {Ix : Type} [Fintype Ix] (e : (Σ τ : T, Fin (r τ)) × Fin n → Ix) (cp : Ix → Fin n) (u' : Ix → Fin d → k)
    (hcp : ∀ p, cp (e p) = p.2) (hu' : ∀ p, u' (e p) = u p.1) :
    Formalism.L2.Pj.nabValN B₂ k h w0 q (boxSer f') cp u' (MvPolynomial.rename e Q) =
      ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h₀ w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) := by
  obtain ⟨h', hh', hval⟩ := exists_gauge hr B₂ hF hA hG h₀ hh₀
  rw [nabValN_boxSer R' d O B₂ k h w0 (const_gauge hh) q n f' _ Ix e cp u u' hcp hu' Q,
    canonGauge_independence_harmonic R' d O k B₂ h h' hh hh' T r cc (fun _ => True) σ hcc (fun _ => Or.inl trivial)
      hσ hsep u hu n Q (fun τ _ => hQ τ) w0 q f']
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [Finset.prod_congr rfl fun b _ => hval w0 q (f b) (f' b) (hf b) _ u (MvPolynomial.monomial (colM mo b) 1)]

end GlobalTheory.Transfer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory



theorem transfer_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (tors : P.TorsionIso) (ϖ : T.V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v), letI := io.toAlgebra; ∃ x hx j hj u hu B hB ρ hρ, B.G.F = C.FT ∧ B.A.act = C.actT ∧ ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (s : Fin n → Fam P.D.toPre F g') (s' t : Fin n → Fam P.D.toPre F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)), (∀ b, NuGe P.D Q F v g' (s b) 0 ∧ PullAl P.D F P.oD (star π) g' g (s b) (s' b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Transl (g' * g) π (s' b) (t b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Germ (g' * g) (t b) (f b)) → ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g)) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A) (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) (un : PS T.V 1 (chD C.ch)), BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' h ∧ MvPowerSeries.constantCoeff un = 1 ∧ h = boxSer (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un) ∧ ∀ h₀ : PS F 2 (chD C.ch), B.IsCanonGauge F h₀ → ∀ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (Pp : MvPolynomial ((Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n) F), (∀ (τ : E →+* ℂ) (i : Fin (rk τ)) (i' : Fin (rk (ComplexEmbedding.conjugate τ))), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) (MvPolynomial.pderiv ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) Pp) = 0) → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n)) Pp) = (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).colVal h₀ (g' * g) (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) Pp f := by
  intro L1 L2 L4 TW E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hFr P tors ϖ hϖ Q hQ F _ _ _ _ _ _ v hv
  letI := io.toAlgebra
  haveI := T.cpl
  obtain ⟨BT, e1, e2, e3, e4, e5, e6, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨hF, hA, hG, hcan⟩ := e7 F
  obtain ⟨τ, hτ, hEL, -⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hrel, hgerm⟩ := GlobalTheory.T.chartFromPointDatum_of_laws L1 L2 L4 TW E H T.V T.cpl C.I.G P tors ϖ hϖ
    Q hQ F v hv (chD C.ch) BT C.tgT C.xT C.eT C.wPT (by rw [e1, e2]; exact C.chartT)
    (by rw [e1, e2, e3, e4, e5, e6]; exact C.frameT) C.primT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C) hFr τ hτ
    (by rw [e2]; exact hEL)
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, (Transfer.law_eq hrel).trans e1, (Transfer.act_eq hrel).trans e2, ?_⟩
  intro g g' π hg hg' hπ n D' A' G' _ _ pD pA pG U' PU _ oD' hxe hon s s' t f hcol
  obtain ⟨un, hun1, hun⟩ := Transfer.exists_inv_pow _ (Transfer.const_diagSer hrel H.w0) (g' * g)
  have hf : ∀ b, (f b * MvPowerSeries.map (algebraMap T.V F) un) *
      MvPowerSeries.map (algebraMap T.V F) (diagSer BT H.w0 ε) ^ (g' * g) = f b := fun b => by
    rw [_root_.mul_assoc, ← map_pow, ← map_mul, hun, map_one, _root_.mul_one]
  choose σ hσ1 hσ2 using fun b => hgerm (g' * g) (t b) (f b) _ (hcol b).2.2.2 (hf b)
  choose p xx w ζ t₀ h1 h2 h3 h4 h5 h6 h7 using fun b => (hcol b).2.2.1
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', hbox, -⟩ := GlobalTheory.T.boxTupSt_of_laws_of_twistBaseChange L1 L2 L4 TW E H Dw l Xo c T io y C P ϖ hϖ Q hQ F v
    g g' π hg hg' hπ τ hτ hEL n D' A' G' pD pA pG U' PU oD' hxe hon s s' t₀ t p w ζ xx σ
    (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un)
    (fun b => ⟨(hcol b).1, (hcol b).2.1, h3 b, h4 b, h5 b, h1 b, h2 b, h6 b, h7 b, hσ1 b, hσ2 b⟩)
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', _, un, hbox, hun1, rfl, ?_⟩
  intro h₀ hh₀ rk hrk Pp hPp
  have huv : ∀ ℓ i, algebraMap T.Fr F (C.ch.uvec ℓ i) = algebraMap T.V F (C.uvecT ℓ i) := fun ℓ i => by
    rw [C.gen.1.2.2.2.2.2.2 ℓ i, ← IsScalarTower.algebraMap_apply]
  refine Transfer.value_eq hrel C.ch.B hF hA hG h₀ _ hh₀ hcan rk ComplexEmbedding.conjugate
    (fun τ => (algebraMap T.Fr F).comp (io.comp (embK c τ))) (fun τ => ComplexEmbedding.involutive_conjugate E τ) ?_ ?_
    (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) ?_ Pp hPp
    H.w0 (g' * g) f _ hf
    (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n))
    (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
    (fun _ => rfl) (fun p => funext fun i => huv _ i)
  · intro τ a
    have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    exact congrArg (fun z => algebraMap T.Fr F (io z)) h
  · intro τ τ' hne
    obtain ⟨a, ha⟩ := EigDir.embK_sep c τ τ' hne
    refine ⟨a, ?_⟩
    simp only [RingHom.comp_apply]
    rw [← map_sub, ← map_sub]
    exact ((isUnit_iff_ne_zero.2 (sub_ne_zero.2 ha)).map io).map _
  · intro ℓ a
    have h := Transfer.eig_map (k := F) C.ch.B a _ _
      (eigDirSt E H Dw l Xo c T io y C a ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩)
    have e : (fun i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩ i)) =
        fun i => algebraMap T.V F (C.uvecT ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩ i) := funext fun i => huv _ i
    exact e ▸ h

end GlobalTheory
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProd

theorem product_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (l ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a, lenA k r z (Matrix.of x) a ^ 2) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν hnz
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  obtain ⟨w, hw1, -, hwK, hwF⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hK k r _ _ (R ν) hDS Q (E ν) hQ (hE ν hν0).1
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDS Q (E ν) hQ (hE ν hν0).1
  have hLev := GlobalTheory.lev_zero_of_kHighest _ _ _ (E ν) _ w hMod.1 hMod.2.1 hwK hwF
  have hw1' : ‖(w : (R ν).H)‖ = 1 := hw1
  have hwsm : (w : (R ν).H) ∈ (R ν).sm := w.2
  refine ⟨(w : (R ν).H), hwsm, hw1', ?_⟩
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hq2 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hmain := GlobalTheory.T.product_moment_bound_density_mass_one (Formalism.QuantumDeterminants.Mt k r) νq r (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
    hlen
    (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
    (((hmeas (l ν) hBeL.1 w hwsm).norm.aemeasurable.pow_const 2).const_mul _)
    (fun x => mul_nonneg hdg.le (by positivity))
    (by
      have := ((GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 w hwsm
      simpa only [one_mul, hw1', one_pow, ENNReal.ofReal_one] using this)
    hA (one_le_pow₀ hb)
    (fun q hq => by
      have := GlobalTheory.T.family_setup_cayley_recursion hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q ν
        (by omega) 0 (hq2 q hq) w hLev
      simpa only [hw1, one_pow, mul_one] using this)
    (fun a q hq => by
      have := GlobalTheory.T.family_setup_cayley_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0
        0 q (hq2 q hq) a w hLev
      simpa only [hw1, one_pow, mul_one] using this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (by positivity))
    (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hNum hT) _

end GlobalTheory.MomProd
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_foldCapelli_sesquilinear : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∀ (a : ℂ) (X X' Z Z' : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) X' → B.InCC A (5 + w.length * (2 * r + k + 1)) X → B.InCC A (5 + w.length * (2 * r + k + 1)) X' → B.InCC A 5 Z → B.InCC A 5 Z' → B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • X') w) Z = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X') w) Z ∧ B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (Z + a • Z') = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + (starRingEnd ℂ) a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA a X X' Z Z' hX hX' hXc hX'c hZ hZ'
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.capelliWordProduct_decayBound_uniform k r Wp Wq s w 5
  obtain ⟨c, hc⟩ := hXc
  obtain ⟨c', hc'⟩ := hX'c
  have h1 : B.InCC A 5 _ := ⟨_, hK A c X hX hc⟩
  have h2 : B.InCC A 5 _ := ⟨_, hK A c' X' hX' hc'⟩
  refine ⟨?_, (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA hZ hZ' h1 a).2⟩
  rw [← (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA h1 h2 hZ a).1]
  exact Formalism.FourierDecayAlt.P.JCx2.sq_beta_congr Bs (fun g hg => GlobalTheory.capelliFold_add_smul k r Wp Wq s w a X X' hX hX' g hg)

end GlobalTheory
end
