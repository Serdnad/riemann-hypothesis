module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle012
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle016

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

section Alg

variable {S : Type} [CommRing S] (d : ℕ)

abbrev swJ (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
      p.1 p.2

private theorem jetSubstP_apply_mk {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S)
    (p : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) p) := by
  rfl

private theorem degree_eq_sum_lemma_2 {τ : Type} (e : τ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree, Finsupp.sum]

private theorem le_degree_lemma_4 {τ : Type} (e : τ →₀ ℕ) (i : τ) : e i ≤ e.degree := by
  by_cases h : e i = 0
  · rw [h]; exact Nat.zero_le _
  · rw [degree_eq_sum_lemma_2]
    exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.2 h)

private theorem mem_degLE_lemma_6 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (e : τ →₀ ℕ) :
    e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨_, h⟩
    rw [degree_eq_sum_lemma_2]
    exact h
  · intro h
    refine ⟨⟨fun i => ⟨e i, by have := le_degree_lemma_4 e i; omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · ext i
      simp
    · rw [degree_eq_sum_lemma_2] at h
      exact h

private theorem coeff_psTrunc_lemma_7 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f : MvPowerSeries τ S) (e : τ →₀ ℕ) :
    AddMonoidAlgebra.coeff (psTrunc m f) e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  rw [psTrunc, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_degLE_lemma_6]

theorem mk_psTrunc_X {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (q : τ) :
    (Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m (MvPowerSeries.X q))) = Ideal.Quotient.mk _ (X q) := by
  have hdeg : (Finsupp.single q 1).degree = 1 := by
    rw [degree_eq_sum_lemma_2, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same]
  have hs : psTrunc m (MvPowerSeries.X q : MvPowerSeries τ S) = if 1 ≤ m then X q else 0 := by
    ext e
    rw [coeff_psTrunc_lemma_7, MvPowerSeries.coeff_X]
    by_cases h2 : e = Finsupp.single q 1
    · subst h2
      rw [hdeg]
      by_cases h3 : 1 ≤ m
      · simp [h3, MvPolynomial.coeff_X]
      · simp [h3]
    · have h4 : AddMonoidAlgebra.coeff (X q : MvPolynomial τ S) e = 0 := by
        rw [MvPolynomial.coeff_X']
        exact if_neg (Ne.symm h2)
      split_ifs <;> simp [h4, h2]
  rw [Ideal.Quotient.eq, hs]
  split_ifs with h
  · rw [sub_self]
    exact Ideal.zero_mem _
  · have hm : m = 0 := by omega
    subst hm
    rw [zero_sub, zero_add, pow_one]
    exact Ideal.neg_mem_iff _ |>.2 (Ideal.subset_span ⟨q, rfl⟩)

private theorem jetMap_mk_lemma_13 {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (hφ : ∀ i, φ i ∈ orig S κ')
    (p : MvPolynomial κ S) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := by
  rfl

end Alg

section Axes

variable {S : Type} [CommRing S] (d : ℕ)

abbrev axJ (m : ℕ) (b : Bool) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (if b then ![fun _ => 0, fun j => X ((0 : Fin 1), j)] else ![fun j => X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

def axV (b : Bool) (k : Fin 2) (j : Fin d) : MvPolynomial (Fin 1 × Fin d) S :=
  if (k = 1) = b then X ((0 : Fin 1), j) else 0

theorem axJ_X (m : ℕ) (b : Bool) (k : Fin 2) (j : Fin d) :
    axJ (S := S) d m b (Ideal.Quotient.mk _ (X (k, j))) = Ideal.Quotient.mk _ (axV d b k j) := by
  rw [jetSubstP_apply_mk, aeval_X]
  cases b <;> fin_cases k <;> simp [axV]

theorem psTrunc_zero {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) :
    psTrunc m (0 : MvPowerSeries τ S) = 0 := by
  simp [psTrunc]

theorem psJet_ev_ax (m : ℕ) (f : PS S 2 d) (b : Bool) :
    psJet m (ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) f) = axJ d m b (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin 2 × Fin d => ((if b then ![0, pt S d 0] else ![pt S d 0, 0]) : Fin 2 → Pt S 1 d) p.1 p.2) p) = 0 := by
    rintro ⟨i, j⟩
    cases b <;> fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [psJet_subst m _ ha f]
  refine DFunLike.congr_fun ?_ (psJet m f)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [axJ_X, jetMap_mk_lemma_13, aeval_X]
  cases b <;> fin_cases k <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, mk_psTrunc_X, axV, psTrunc_zero]

end Axes

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem scaleGenG_scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (v w : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε v (scaleGenG t φ ε w g) = scaleGenG t φ ε (v * w) g := by
  simp only [scaleGenG, Units.val_mul, map_mul, mul_assoc]

theorem unitΓ_mul {A : Type} [CommRing A] (a b : Aˣ) : unitΓ (a * b) = unitΓ a * unitΓ b := by
  exact map_mul (Units.map (toΓ A).toMonoidHom) a b

theorem unitΓ_one {A : Type} [CommRing A] : unitΓ (1 : Aˣ) = 1 := by
  exact map_one (Units.map (toΓ A).toMonoidHom)

end Frame

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

namespace H1algLink

open Formalism.L2.Pj.Crude

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem liesOver_resChar : la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := resCharOf_prime la
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ la.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) ((resCharOf la : ℕ) : ℤ) ∈ la.asIdeal
    rw [map_natCast]
    exact crv_char_mem la
  have hne : la.asIdeal.under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ la.asIdeal.under ℤ := by rw [h]; trivial
    change algebraMap ℤ (𝓞 K) 1 ∈ la.asIdeal at h1
    rwa [map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem span_resChar_ne_bot : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (resCharOf_prime la).ne_zero

theorem eWL_eq : eWL K la = ramOverZ la := by
  have := liesOver_resChar la
  unfold eWL ramOverZ
  exact (Ideal.ramificationIdx'_eq_ramificationIdx _ _ (span_resChar_ne_bot la)).symm

theorem ramOverZ_ne_zero : ramOverZ la ≠ 0 := by
  have := liesOver_resChar la
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la.asIdeal (span_resChar_ne_bot la)

theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hnd : ¬ resCharOf la ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq (resCharOf_prime la) hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

variable {D : D7}

end H1algLink


end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem intChart_of_cut (hA : ChartDataGSt) (hB : FrameSt) (hC : FBIdSt) (hGF : GlobalFnsSt) :
    IntChartStatement := by
  intro E _ _ _ H V _ _ _ hc t hprop κ _ tg htan hbas _ hstar
  obtain ⟨d, G, A, uvec, x, hd, hu, hch⟩ := hA E H (Sp V) t V (𝟙 (Sp V)) tg htan hbas
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    hB E H (Sp V) t V (𝟙 (Sp V)) d G A κ tg uvec x hch
  have hPow := globalFnsDvr_of_globalFns hGF E H V hc t hprop
  obtain ⟨hax, hr⟩ := hC E H (Sp V) t hPow hstar V (𝟙 (Sp V)) d G A κ tg uvec x e ph1 ph2 sy ad hch hfr hfa had
  refine ⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, hd, hu, hch, hfr, hpr, htr, hrig, fun k F => ?_⟩
  exact germSt_holds E H (Sp V) t V (𝟙 (Sp V)) d G.F A.act κ tg uvec x ph1 ph2 sy ad e wP hch hfr hpr htr k F

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def ExpPowSt : Prop :=
  ∀ (S σ : Type) [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S), MvPowerSeries.constantCoeff q = 0 →
    ∀ k : ℕ, PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1

theorem gaugeUniq_of' (hB : BetaUniqSt) (hR : GaugeRatioSt) (hP : ExpPowSt) : GaugeUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x hx e e' he he'
  have hL := Xo.univ.t.PP.isLB
  choose u hu using fun m => ratio_of_gen Xo.univ.t.PP.L hL (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ))
    (e m) (e' m) (he.gen m) (he'.gen m)
  let g : ∀ m, Jet S (Fin 1 × Fin (dL Dw)) m := fun m => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (u m).val
  have hpull : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (f : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] B),
      gam B (pullUnit (homAt y.x f).left (u m)).val = f (g m) := fun m B _ _ f =>
    gam_pullUnit (f : Jet S (Fin 1 × Fin (dL Dw)) m →+* B) (u m)
  have htr : ∀ m, jetTrunc (g (m + 1)) = g m := by
    intro m
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] _)).left (hu (m + 1))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (hu m) (he.trunc m) (he'.trunc m)
    have h2 := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    exact (hpull (m + 1) _ jetTrunc).symm.trans h2
  obtain ⟨r, hr⟩ := exists_ps_of_compat g htr
  have hrig : MvPowerSeries.constantCoeff r = 1 := by
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left (hu 0)
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (scaled_one _) he.rig he'.rig
    have h2 := congrArg (fun v => gam S (Units.val v)) hU
    simp only [Units.val_one, map_one] at h2
    rw [← jetAug_psJet 0 r, hr 0]
    exact (hpull 0 S jetAug).symm.trans h2
  have hid : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r *
        MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r := by
    intro a
    obtain ⟨β, hβg, hβr, hβc⟩ := he.coc a
    obtain ⟨β', hβ'g, hβ'r, hβ'c⟩ := he'.coc a
    obtain rfl := hB E H Dw l Xo a β β' hβg hβ'g hβr hβ'r
    refine GermFun.psJet_inj fun m => ?_
    have s1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a)))).left (hu m)
    have sa := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left (hu m)
    have sb := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a)))).left (hu m)
    have srhs := scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_one (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left))
      (scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_genPow _ _ sa 2) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (hu m) sb))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ s1 srhs (hβc m) (hβ'c m)
    have hv := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, one_mul] at hv
    rw [hpull, hpull, hpull] at hv
    have hv' : jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (1 + a * H.bar a) i) * MvPolynomial.X i) (g m) =
        jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S a i) * MvPolynomial.X i) (g m) ^ 2 *
          (g m * jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (a * H.bar a) i) * MvPolynomial.X i) (g m)) :=
      hv
    rw [psJet_mul, psJet_mul, psJet_pow, ← jetSubstP_scale, ← jetSubstP_scale, ← jetSubstP_scale, hr m, hv']
    ring
  obtain ⟨q, hq0, hdeg, hpair, hexp⟩ := ratio_exp hR c S r hrig hid
  refine ⟨q, hq0, hdeg, hpair, fun k F f f' hf hf' => ?_⟩
  refine GermFun.psJet_inj fun m => ?_
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hf' m
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have sg := scaled_genPow (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (hu m) k
  have sτ := corr_scaled_left Xo.univ.t.PP.L hL (x m).left (k : ℤ) _ _ τ₁ τ₂ _ _ _ sg hC₁ hC₂
  have hval := value_scaled Xo.univ.t.G Xo.univ.t.PP.L hL (k : ℤ) _ (x m) τ₁ τ₂ _ _ _ hV₁ hV₂ sτ
  have hg := congrArg (gam (Jet S (Fin 1 × Fin (dL Dw)) m)) hval
  rw [gam_toΓ, map_mul, gam_toΓ, Units.val_pow_eq_pow_val, map_pow] at hg
  have hpow := congrArg (psJet m) (hP S _ q hq0 k)
  rw [psJet_mul, psJet_pow, ← hexp, hr m, psJet_one] at hpow
  rw [psJet_mul, hg]
  calc psJet m f' = psJet m f' * (g m ^ k * psJet m (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S))) := by
        rw [hpow, mul_one]
    _ = _ := by ring

end GaugeR

theorem gaugeUniq_of (hB : BetaUniqSt) : GaugeUniqSt :=
  GaugeR.gaugeUniq_of' hB GRPf.gaugeRatio fun _ _ _ _ q hq k => GaugeR.exp_pow_mul_exp_neg q hq k

theorem gaugeUniq_of_global (hG : GlobalFnsSt) : GaugeUniqSt :=
  gaugeUniq_of (betaUniq_of_global hG)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

attribute [local simp] MvPolynomial.bind₁

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem push_inj {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {a b : T ⟶ G'}
    (e : pushHom h T a = pushHom h T b) : a = b := by
  have e1 : a.left ≫ φ = b.left ≫ φ := congrArg (fun z => z.left) e
  have e2 : a.left ≫ G'.hom = b.left ≫ G'.hom := by
    rw [Over.w a, Over.w b]
  exact Over.OverMorphism.ext (h.1.hom_ext e1 e2)

theorem jetCoef_copy {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) (d m n : ℕ) (i : Fin n) :
    (jetCoef f (Fin n × Fin d) m).comp ((jetCopy (S := V) d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) :
      Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m) =
    ((jetCopy (S := K) d m i : Jet K (Fin 1 × Fin d) m →ₐ[K] Jet K (Fin n × Fin d) m) :
      Jet K (Fin 1 × Fin d) m →+* Jet K (Fin n × Fin d) m).comp (jetCoef f (Fin 1 × Fin d) m) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.C r))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.C r)))
    simp
  · intro q
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.X q))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.X q)))
    simp

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

def U2 (m : ℕ) : Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ jOG (𝟙 (Sp T.V)) d m 2 :=
  Over.homMk (spMap (jc (d := d) 2 m)) (by
    show spMap (jc (d := d) 2 m) ≫ spMap (algebraMap T.V (Jet T.V (Fin 2 × Fin d) m)) ≫ 𝟙 _ =
      (spMap (algebraMap T.Fr (Jet T.Fr (Fin 2 × Fin d) m)) ≫ 𝟙 _) ≫ spMap (algebraMap T.V T.Fr)
    rw [Category.comp_id, Category.comp_id, spMap_comp', spMap_comp', jetCoef_alg])

theorem push_jpt (m : ℕ) (i : Fin 2) :
    pushHom I.m2.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) = U2 (d := d) m ≫ jptG I.G (𝟙 (Sp T.V)) d xT m i := by
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_copy]

theorem xP_law (FT : Fin d → MvPowerSeries (Fin 2 × Fin d) T.V) (m : ℕ)
    (hl : Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (FT p.2)) ≫ xT m =
      jptG I.G (𝟙 (Sp T.V)) d xT m (0 : Fin 2) * jptG I.G (𝟙 (Sp T.V)) d xT m (1 : Fin 2)) :
    Formalism.L2.Pj.homAt (𝟙 (Sp T.Fr)) (jetSubstP m fun p : Fin 1 × Fin d =>
              MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (FT p.2))) ≫ xP I xT m =
      jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (0 : Fin 2) * jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (1 : Fin 2) := by
  apply push_inj I.m2.cart
  rw [map_mul, push_jpt, push_jpt, ← MonObj.comp_mul, ← hl]
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_substP]

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end
