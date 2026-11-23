module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle011
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}

theorem hasSubst_pts {m n : ℕ} {a : Fin m → Pt S n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

theorem map_ev {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS S m d) :
    map ψ (ev a f) = ev (fun j i => map ψ (a j i)) (map ψ f) := by
  simp only [ev]
  exact MvPowerSeries.map_subst (hasSubst_pts ha) f

theorem const_ev {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS S m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have hs := hasSubst_pts ha
  simp only [ev]
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ (0 : Fin m × Fin d →₀ ℕ)]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    simp only [Finsupp.prod, map_prod, map_pow, ha]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (zero_pow hs'), smul_zero]

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ S) :
    map ψ (pderiv i f) = pderiv i (map ψ f) := by
  ext n
  simp [MvPowerSeries.coeff_pderiv]

theorem map_nsmul' {σ : Type} (k : ℕ) (g : MvPowerSeries σ S) :
    map ψ ((k : S) • g) = (k : S') • map ψ g := by
  ext n
  simp

theorem map_eval_first_point_zero (g : PS S 2 d) :
    map ψ (ev (n := 1) ![pt S d 0, 0] g) = ev (n := 1) ![pt S' d 0, 0] (map ψ g) := by
  have h0 : ∀ j i, constantCoeff ((![pt S d 0, 0] : Fin 2 → Pt S 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  rw [map_ev ψ _ h0 g]
  congr 1
  funext j i
  fin_cases j <;> simp [pt]

theorem map_Dof (F : Fin d → PS S 2 d) (v : Fin d → S) (f : PS S 1 d) :
    map ψ (Dof F v f) = Dof (fun j => map ψ (F j)) (fun i => ψ (v i)) (map ψ f) := by

  simp only [Dof, map_sum, map_mul, MvPowerSeries.map_C, map_eval_first_point_zero, map_pderiv]

theorem map_iter_Dof (F : Fin d → PS S 2 d) (v : Fin d → S) (k : ℕ) (f : PS S 1 d) :
    map ψ ((Dof F v)^[k] f) = (Dof (fun j => map ψ (F j)) (fun i => ψ (v i)))^[k] (map ψ f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, map_Dof]

theorem map_DmonOf (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S) (e : κ →₀ ℕ)
    (f : PS S 1 d) :
    map ψ (DmonOf F u e f) = DmonOf (fun j => map ψ (F j)) (fun l i => ψ (u l i)) e (map ψ f) := by
  simp only [DmonOf]
  induction (Finset.univ : Finset κ).toList with
  | nil => rfl
  | cons l L ih => simp only [List.foldr_cons, map_iter_Dof, ih]

theorem map_DpolyOf (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S)
    (P : MvPolynomial κ S) (f : PS S 1 d) :
    map ψ (DpolyOf F u P f) =
      DpolyOf (fun j => map ψ (F j)) (fun l i => ψ (u l i)) (MvPolynomial.map ψ P) (map ψ f) := by

  simp only [DpolyOf, map_sum, map_mul, MvPowerSeries.map_C, map_DmonOf, MvPolynomial.coeff_map]
  symm
  apply Finset.sum_subset (MvPolynomial.support_map_subset ψ P)
  intro e _ he
  have h0 : ψ (P.coeff e) = 0 := by
    simpa [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] using he
  simp [h0]

variable [Algebra ℚ S] [Algebra ℚ S']

theorem map_expS {n : ℕ} (g : PS S n d) (hg : constantCoeff g = 0) :
    map ψ (FB.expS S g) = FB.expS S' (map ψ g) := by
  simp only [FB.expS]
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg), PowerSeries.map_exp]

variable {O : Type} [CommRing O] [StarRing O]

theorem hid (R : Type) [CommRing R] : algebraMap R R = RingHom.id R := rfl

theorem const_comp1_act (B : FB S d O) (a : O) (i : Fin d) :
    constantCoeff (comp1 (B.actK S a) (pt S (n := 1) d 0) i) = 0 := by
  have h1 : ∀ j l, constantCoeff ((![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) j l) = 0 := by
    intro j l
    fin_cases j
    simp [pt]
  simp only [comp1]
  rw [const_ev _ h1]
  simp [FB.actK, B.A.const]

theorem const_pair (B : FB S d O) (w0 : O) :
    ∀ j i, constantCoeff ((![pt S d 0, comp1 (B.actK S w0) (pt S d 0)] : Fin 2 → Pt S 1 d) j i) = 0 := by
  intro j i
  fin_cases j
  · simp [pt]
  · simpa using const_comp1_act B w0 i

theorem map_hL (B : FB S d O) (B' : FB S' d O) (hA : ∀ a i, B'.A.act a i = map ψ (B.A.act a i))
    (h : PS S 2 d) (w0 : O) : map ψ (B.hL S h w0) = B'.hL S' (map ψ h) w0 := by
  have h1 : ∀ j l, constantCoeff ((![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) j l) = 0 := by
    intro j l
    fin_cases j
    simp [pt]
  simp only [FB.hL]
  rw [map_ev ψ _ (const_pair B w0)]
  congr 1
  funext j i
  fin_cases j
  · simp [pt]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, comp1]
    rw [map_ev ψ _ h1]
    congr 1
    · funext j l
      fin_cases j
      simp [pt]
    · simp [FB.actK, hid, hA]

theorem const_hL (B : FB S d O) (h : PS S 2 d) (hh : B.IsCanonGauge S h) (w0 : O) :
    constantCoeff (B.hL S h w0) = 0 := by
  simp only [FB.hL]
  rw [const_ev _ (const_pair B w0)]
  have h2 : ∀ j i, constantCoeff ((![0, pt S (n := 1) d 0] : Fin 2 → Pt S 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  have h3 := congrArg constantCoeff hh.ax0
  rwa [const_ev _ h2, map_zero] at h3

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CIndBCNab

theorem nabMap_holds : NabMapSt := by
  intro S S' _ _ _ _ ψ d O _ _ B B' hF hA h hh w0 m f κ _ u P
  have hc : constantCoeff ((m : S) • B.hL S h w0) = 0 := by
    simp [MvPowerSeries.smul_eq_C_mul, const_hL B h hh w0]
  have hFK : (fun j => MvPowerSeries.map ψ (B.FK S j)) = B'.FK S' := by
    funext j
    simp [FB.FK, FGLaw.mapF, hF, hid]
  simp only [FB.nabVal]
  rw [← MvPowerSeries.constantCoeff_map, map_DpolyOf, map_mul, map_expS ψ _ hc, map_nsmul',
    map_hL ψ B B' hA, hFK]

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

section

variable {E : Type} [Field E] [NumberField E] {cj : E → E} {Y : Type} [AddCommGroup Y]
  [Module (𝓞 E) Y]

theorem two_mul_form_half_unit (hcj : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) (w₀ : 𝓞 E)
    (hw : (w₀ : E) + cj w₀ = 1) (γ : SymB cj Y) (a : Y) :
    2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a := by
  obtain ⟨w', hw'⟩ := hcj w₀
  have mem : (∀ a d : Y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) d a) ∧
      ∀ (c c' : 𝓞 E), (c' : E) = cj c → ∀ (a d : Y),
        (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • a) d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a (c' • d) := γ.2
  have h1 : w₀ + w' = 1 := by
    apply RingOfIntegers.ext
    first
      | (push_cast; rw [hw', hw])
      | simp [hw', hw]
  have h2 : (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w' • a) a := by
    rw [mem.2 w₀ w' hw' a a, mem.1]
  have h3 : (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) ((w₀ + w') • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a := by
    rw [h1, one_smul]
  rw [add_smul, map_add (f := _), LinearMap.add_apply, ← h2] at h3
  linarith

end

theorem bil_rad {Y : Type} [AddCommGroup Y] (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)
    (hsym : ∀ a b, γ a b = γ b a) (hpsd : ∀ a, 0 ≤ γ a a) (a : Y) (ha : γ a a = 0) (y : Y) :
    γ a y = 0 := by
  have key : ∀ n : ℤ, 0 ≤ (n : ℝ) * γ a y + (n : ℝ) * γ a y + γ y y := by
    intro n
    have h := hpsd (n • a + y)
    simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, zsmul_eq_mul, ha,
      hsym y a, mul_zero, zero_add] at h
    linarith
  by_contra hs
  obtain ⟨N, hN⟩ := exists_nat_gt (γ y y / (2 * |γ a y|))
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have h := key N
    rw [abs_of_neg hneg, div_lt_iff₀ (by linarith)] at hN
    push_cast at h
    nlinarith
  · have h := key (-(N : ℤ))
    rw [abs_of_pos hpos, div_lt_iff₀ (by linarith)] at hN
    push_cast at h
    nlinarith

theorem phiCSpan_holds : PhiCSpanStatement := by
  intro E _ _ cj hcj Y _ _ w₀ hw β hβ k x hx
  unfold phiC
  let l : SymB cj Y →ₗ[ℝ] ℝ :=
    { toFun := fun γ => ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i)
      map_add' := fun γ γ' => by simp [Finset.sum_add_distrib]
      map_smul' := fun r γ => by simp [Finset.mul_sum] }
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨l', -, hpos, he⟩
    by_cases h0 : β = 0
    · rw [he, h0, map_zero]
    · rw [he]
      exact (hpos β hβ h0).le
  · refine ⟨l, ?_, ?_, rfl⟩
    · intro γ hγ
      choose z hz using fun i => hγ (w₀ • x i) (x i)
      refine ⟨∑ i, z i, ?_⟩
      show ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) = ((∑ i, z i : ℤ) : ℝ)
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun i _ => hz i
    · intro γ hγ hne
      have mem : (∀ a d : Y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) d a) ∧
          ∀ (c c' : 𝓞 E), (c' : E) = cj c → ∀ (a d : Y),
            (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • a) d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a (c' • d) := γ.2
      have hsum : ∀ i, 2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) =
          (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x i) := fun i => two_mul_form_half_unit hcj w₀ hw γ (x i)
      have hnn : ∀ i, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) := fun i => by
        have := hγ (x i)
        linarith [hsum i]
      show 0 < ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i)
      rcases (Finset.sum_nonneg fun i _ => hnn i).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        apply hne
        have hz : ∀ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x i) = 0 := by
          intro i
          have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp heq.symm i
            (Finset.mem_univ i)
          linarith [hsum i]
        have hrad : ∀ i y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) y = 0 :=
          fun i y => bil_rad _ mem.1 hγ (x i) (hz i) y
        have hspan : ∀ u ∈ Submodule.span (𝓞 E) (Set.range x), ∀ y,
            (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) u y = 0 := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem u hu =>
            obtain ⟨i, rfl⟩ := hu
            exact hrad i
          | zero => intro y; simp
          | add u v _ _ hu hv => intro y; simp [hu y, hv y]
          | smul c u _ hu =>
            intro y
            obtain ⟨c', hc'⟩ := hcj c
            rw [mem.2 c c' hc' u y]
            exact hu _
        apply Subtype.ext
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        obtain ⟨n, hn, hny⟩ := hx y
        have h1 := hspan _ hny z
        simp only [map_nsmul, map_zsmul, LinearMap.smul_apply, nsmul_eq_mul, zsmul_eq_mul] at h1
        rw [show ((0 : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) = 0 from rfl, LinearMap.zero_apply,
          LinearMap.zero_apply]
        rcases mul_eq_zero.mp h1 with h | h
        · first
            | exact absurd h (Nat.cast_ne_zero.mpr hn.ne')
            | exact absurd h (Int.cast_ne_zero.mpr hn.ne')
        · exact h

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts ComplexConjugate

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def bs (b : Basis ι ℤ Y) (a : ι) : Y →ₗ[ℤ] ℝ := Algebra.linearMap ℤ ℝ ∘ₗ b.coord a

theorem bs_apply (b : Basis ι ℤ Y) (a : ι) (y : Y) : bs b a y = (b.repr y a : ℝ) := by
  simp [bs]

theorem gram_expand (b : Basis ι ℤ Y) (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (v w : Y) :
    ∑ a, ∑ c, β (b a) (b c) * (bs b a v * bs b c w) = β v w := by
  conv_rhs => rw [← b.sum_repr v, ← b.sum_repr w]

  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, bs_apply, zsmul_eq_mul,
  Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

section Repro

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem repro_sigma (b : Basis ι ℤ Y) (β : SymB cj Y) (σ : E →+* ℂ) (y z : Y) :
    ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z)) =
      comp ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ).flip z) σ y := by
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB
  obtain ⟨_, hbal⟩ := β.2

  have hj : ∀ j, ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) * σ (ed E i)
      = star (σ (RingOfIntegers.basis E j : E)) * comp (B.flip z) σ y := by
    intro j
    obtain ⟨c, hc⟩ := cj_integral hcj (RingOfIntegers.basis E j)
    have hcc : ((RingOfIntegers.basis E j : 𝓞 E) : E) = cj (c : E) := by rw [hc, cj_cj hcj]
    have e : ∀ i, B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) =
        B (RingOfIntegers.basis E i • (c • y)) z := by
      intro i
      rw [← hbal c _ hcc, smul_comm]
    simp_rw [e]
    rw [show ∑ i, (B (RingOfIntegers.basis E i • (c • y)) z : ℂ) * σ (ed E i) = comp (B.flip z) σ (c • y)
      from rfl, comp_smul, hc, hcj]
  have e2 : ∀ c, conj (comp (bs b c) σ z) =
      ∑ j, (bs b c (RingOfIntegers.basis E j • z) : ℂ) * conj (σ (ed E j)) := by
    intro c

    simp [comp, map_sum]
  have expand : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z)) =
      ∑ j, conj (σ (ed E j)) * ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) *
        σ (ed E i) := by
    simp_rw [← gram_expand b B (RingOfIntegers.basis E _ • y) (RingOfIntegers.basis E _ • z)]
    simp_rw [e2]
    simp only [comp, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum,
      Complex.ofReal_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [expand]
  simp_rw [hj]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have ho := ortho σ σ
  simp only [if_true, integralBasis_apply] at ho
  have : ∑ j, conj (σ (ed E j)) * star (σ (RingOfIntegers.basis E j : E)) = 1 := by
    have := congrArg conj ho

    simpa [map_sum, map_mul] using this
  rw [this, one_mul]

theorem fock_reproducing_formula (b : Basis ι ℤ Y) (β : SymB cj Y) (y z : Y) :
    ∑ a, ∑ c, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) * Pf E (bs b a) (bs b c) y z =
      2 * (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z := by
  obtain ⟨hs, _⟩ := β.2
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB
  have key : ∀ σ : E →+* ℂ, ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z) + comp (bs b c) σ y * conj (comp (bs b a) σ z)) =
      2 * comp (B.flip z) σ y := by
    intro σ
    simp only [mul_add, Finset.sum_add_distrib]
    have sw : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b c) σ y * conj (comp (bs b a) σ z)) =
        ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
      rw [hs (b w) (b x)]
    rw [sw, repro_sigma hcj b β σ y z]
    ring
  unfold Pf
  have e : ∀ a c, B (b a) (b c) *
      (∑ σ : E →+* ℂ, (comp (bs b a) σ y * conj (comp (bs b c) σ z) +
        comp (bs b c) σ y * conj (comp (bs b a) σ z))).re =
      (∑ σ : E →+* ℂ, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z) +
        comp (bs b c) σ y * conj (comp (bs b a) σ z))).re := by
    intro a c
    rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  simp_rw [e]
  simp_rw [← Complex.re_sum]
  conv_lhs => arg 1; arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [key]
  rw [← Finset.mul_sum, sum_comp]
  simp [LinearMap.flip_apply]

theorem l_expand (b : Basis ι ℤ Y) (l : SymB cj Y →ₗ[ℝ] ℝ) (β : SymB cj Y) :
    l β = ∑ a, ∑ c, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) * (l (Pm hcj (bs b a) (bs b c)) / 2) := by
  have hsum : β = ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) / 2) • Pm hcj (bs b a) (bs b c) := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro y z
    have hP : ∀ (η ζ : Y →ₗ[ℤ] ℝ), ((Pm hcj η ζ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z = Pf E η ζ y z :=
      fun _ _ => rfl
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, hP,
      smul_eq_mul]
    have := fock_reproducing_formula hcj b β y z
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, this]
    ring
  conv_lhs => rw [hsum]

  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end Repro

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end
