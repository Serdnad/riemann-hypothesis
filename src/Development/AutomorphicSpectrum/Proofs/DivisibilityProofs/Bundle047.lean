module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle234
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle014
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle046
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh

theorem coheight_eq_one_of_dim_closure {X : Scheme.{0}} {n : ℕ}
    (hX : topologicalKrullDim X ≤ (n + 1 : ℕ)) {w : X} (hw : ¬ IsMax w)
    (hd : topologicalKrullDim (closure ({w} : Set X)) = n) : Order.coheight w = 1 := by
  have key : ∀ {a b : X}, a < b → topologicalKrullDim (closure ({a} : Set X)) + 1 ≤
      topologicalKrullDim (closure ({b} : Set X)) := by
    intro a b hab
    refine topologicalKrullDim_add_one_le isClosed_closure isClosed_closure
      fun x hx => ⟨b, subset_closure rfl, fun hb => ?_, ?_⟩
    · exact hab.not_ge (specializes_iff_mem_closure.2 hb)
    · have h1 : b ⤳ a := hab.le
      have h2 : a ⤳ x := specializes_iff_mem_closure.2 hx
      exact h1.trans h2
  have hle : ∀ b : X, topologicalKrullDim (closure ({b} : Set X)) ≤ topologicalKrullDim X :=
    fun b => Topology.IsInducing.subtypeVal.topologicalKrullDim_le
  refine le_antisymm ((Order.coheight_le_coe_iff (n := 1)).2 fun y hy => ?_) ?_
  · by_contra hc
    have hy0 : ¬ IsMax y := fun h => hc (by rw [Order.coheight_eq_zero.2 h]; exact zero_lt_one)
    obtain ⟨b, hyb⟩ := not_isMax_iff.1 hy0
    have h := ((add_le_add (hd ▸ key hy : (n : WithBot ℕ∞) + 1 ≤ _) (le_refl (1 : WithBot ℕ∞))).trans
      (key hyb)).trans ((hle b).trans hX)
    norm_cast at h
    omega
  · rw [ENat.one_le_iff_ne_zero]
    exact fun h => hw (Order.coheight_eq_zero.1 h)

open scoped Pointwise

theorem mult_divOfSec_eq_length_cut {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {M : LB X} (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {w : X}
    (hw : Order.coheight w = 1) :
    (divOfSec hM s hs).mult w = ((Module.length (X.presheaf.stalk w)
      ((cut (structureModule X) hM s).presheaf.stalk w :)).toNat : ℤ) := by
  obtain ⟨i, hi⟩ := exists_chart hM w
  obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv (structureModule X) hM s i hi
  set g := X.presheaf.germ _ w hi (s.f i)
  have e1 : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {g}) =
      Module.length (X.presheaf.stalk w) (QuotSMulTop g (X.presheaf.stalk w)) := by
    refine (Submodule.quotEquivOfEq (Ideal.span {g}) (g • (⊤ : Submodule (X.presheaf.stalk w)
      (X.presheaf.stalk w))) ?_).length_eq
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [mult_divOfSec hw hi, ← q.length_eq,
    (QuotSMulTop.congr g (structureModuleStalkEquiv w)).length_eq, ← e1]

theorem mult_divOfSec_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {M : LB X} (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {w : X}
    (hw : Order.coheight w = 1) (hws : w ∉ nonzeroLocus s) : (divOfSec hM s hs).mult w ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_chart hM w
  have : Ring.KrullDimLE 1 (X.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
  have e := algebraMap_germ hi (s.f i)
  have hg0 : X.presheaf.germ _ w hi (s.f i) ≠ 0 := fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    (e.symm.trans ((congrArg _ h0).trans (map_zero _)))
  have htop := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hg0)
  have hu : ¬ IsUnit (X.presheaf.germ _ w hi (s.f i)) := fun h =>
    hws ((mem_nonzeroLocus_iff s i hi).2 ((Scheme.mem_basicOpen _ _ _ _).2 h))
  rw [mult_divOfSec hw hi, Nat.cast_ne_zero, Ne, ENat.toNat_eq_zero, not_or]
  refine ⟨fun h0 => hu ?_, htop⟩
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at h0
  exact h0

theorem interNum_cons_eq_finsum_mult : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (s : M.Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfSec hM s hs).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ _ _ hproj n hX M hM P hP s hs
  have hf := algebraMap_eq_strHom κ X
  have := isNoetherian_of_isProjOver hproj
  have : IsProper (strHom κ (X := X)) := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hproj
  have hmono := (mono_cutHom_structureModule_iff hM s).2 hs
  have hfin : FiniteCohTwists κ (structureModule X) := hH.finiteCohTwists hf _
  rw [interNum_cons_eq_interNum_cut hM s hP hfin]
  have hsupp : suppDim (cut (structureModule X) hM s) ≤ (Fintype.card (Fin n) : ℕ) := by
    rw [Fintype.card_fin]
    exact suppDim_cut_le _ hM s (by rwa [QCoh.suppDim_structureModule])
  have hfs := (divOfSec hM s hs).finite_support_mult
  have hS : ∀ w ∈ support (cut (structureModule X) hM s),
      topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card (Fin n) : ℕ) → w ∈ hfs.toFinset := by
    intro w hw hd
    rw [Fintype.card_fin] at hd
    rw [support_cut, QCoh.support_structureModule] at hw
    have hmax : ¬ IsMax w := fun h => hw.2 ((h (genericPoint_specializes w) :
      w ⤳ genericPoint X).mem_open (nonzeroLocus s).isOpen hs)
    have hc := coheight_eq_one_of_dim_closure hX hmax hd
    simpa using mult_divOfSec_ne_zero hM s hs hc hw.2
  rw [GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.interNum_eq_sum_length_mul_interNumRed κ X hproj (Fin n) P hP _ hsupp hfs.toFinset hS,
    finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_]
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hw' : (divOfSec hM s hs).mult w ≠ 0 := by simpa using hw
    rw [mult_divOfSec_eq_length_cut hM s hs (CartierDiv.coheight_eq_one_of_mult_ne_zero hw')]
  · intro w hw
    simpa using Function.support_mul_subset_left _ _ hw

end GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem lower_bound_key_inequality (K f m x L C h R : ℝ) (hK : 0 < K) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (h1 : -(C * f * m * L) * K ≤ h - x * (f * (K * m)) + R) (l : ℝ) (h2 : h ≤ K * (f * (m / 2 * l)))
    (h3 : |R| ≤ 1.6 * K) : x ≤ C * L + l / 2 + 1.6 := by
  have hR : R ≤ 1.6 * K := (le_abs_self R).trans h3
  have hfm : 1 ≤ f * m := by nlinarith
  have hP : 0 < f * (K * m) := mul_pos (by linarith) (mul_pos hK (by linarith))
  have hKfm : K ≤ K * (f * m) := by nlinarith
  have key : x * (f * (K * m)) ≤ (C * L + l / 2 + 1.6) * (f * (K * m)) := by
    nlinarith
  exact le_of_mul_le_mul_right key hP

theorem lower_bound_finite_arith (N m A M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) (hN : N ≤ 2 * m) (h : -(N * M) ≤ m * A) : -(2 * M) ≤ A := by
  have h' : m * (-(2 * M)) ≤ m * A := by nlinarith
  exact le_of_mul_le_mul_left h' hm

theorem test_height_bound_slope_flat : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd → T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C' rd Lval → T.SlopeLower II C rd Lval → hh (testPoly T.j) ≤ ((dimX Ψ N T.j : ℝ) + 1) * testDeg Ψ N T.j * (Fintype.card Ψ * ((min T.j (N - T.j) : ℕ) / 2 * Real.log (N + 1))) → T.LowerBoundAtBase II hh frob (2 * (C + C') + 3) rd Lval := by
  intro II Ψ _ _ N T _ hh frob C C' rd Lval hC hC' hrd hprop hI9 hPF hSL hhh B₀ A₀ b₀ hB128 hB4 hbad hId
  have hj1 := T.j_pos
  have hjN := T.j_lt
  obtain ⟨hhom, htd, hcase1, hcase2⟩ := GlobalTheory.T.test_polynomial_shift_total Ψ N T.j hj1 hjN
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.homogeneous_power_sum_decomposition Ψ N (testPoly T.j) (by omega) hhom
  have hdec : IsDecomp (testPoly T.j) Q := ⟨hQ1, hQ2⟩
  have hPP := GlobalTheory.T.tower_height_identity_expansion II Ψ N T hh frob B₀ A₀ b₀ (testPoly T.j) Q hId hdec
  have hR := GlobalTheory.T.test_polynomial_remainder_bound Ψ N T.j T.bad frob B₀ Q hj1 hjN hB4 hdec
  have hAb := GlobalTheory.T.cutoff_coefficients_bound II Ψ N T hh frob C' rd Lval B₀ A₀ b₀ hprop hI9 hPF hB128 hbad hId
  have hSL' := hSL B₀ hB128 hB4 hbad
  have hvol : 0 < T.volT := by
    show 0 < ∑ c, T.vol c
    exact Finset.sum_pos (fun c _ => hprop.1 c) Finset.univ_nonempty
  have hcard : 1 ≤ Fintype.card Ψ := Fintype.card_pos
  have hf : (1:ℝ) ≤ (Fintype.card Ψ : ℝ) := by exact_mod_cast hcard
  have hN1 : N + 1 ≤ B₀ := by nlinarith
  have hlogB : Real.log (B₀:ℝ) ≤ bigLam (B₀:ℝ) rd Lval := by
    show Real.log (B₀:ℝ) ≤ Real.log ((B₀:ℝ) * rd) + |Lval|
    have hB0 : (0:ℝ) < B₀ := by exact_mod_cast (show 0 < B₀ by omega)
    have := Real.log_le_log hB0 (le_mul_of_one_le_right hB0.le hrd)
    linarith [abs_nonneg Lval]
  have hl : Real.log ((N:ℝ) + 1) ≤ Real.log (B₀:ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hN1)
  have hl0 : 0 ≤ Real.log ((N:ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have h16 : 1.6 ≤ Real.log (B₀:ℝ) := by
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128:ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have : Real.log 128 ≤ Real.log (B₀:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hB128)
    linarith [Real.log_two_gt_d9]
  set Λ := bigLam (B₀:ℝ) rd Lval with hΛ
  set R := ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k) with hRdef
  set f : ℝ := (Fintype.card Ψ : ℝ) with hfdef
  set D : ℝ := (dimX Ψ N T.j : ℝ) with hD
  set td := testDeg Ψ N T.j with htddef
  set l := Real.log ((N:ℝ) + 1) with hldef
  have hK : 0 < (D + 1) * td := mul_pos (by positivity) htd
  have hM0 : 0 ≤ C * Λ + l / 2 + 1.6 + C' * Λ := by
    have := mul_nonneg hC (show 0 ≤ Λ by linarith)
    have := mul_nonneg hC' (show 0 ≤ Λ by linarith)
    linarith
  have hfinal : ∀ A : ℝ, -(2 * (C * Λ + l / 2 + 1.6 + C' * Λ)) ≤ A →
      -((2 * (C + C') + 3) * Λ) ≤ A := by
    intro A hA
    nlinarith
  apply hfinal
  have hAb' := abs_le.mp hAb
  by_cases hc : N - T.j ≤ T.j
  · have hs := hcase1 hc
    have hmin : min T.j (N - T.j) = N - T.j := min_eq_right hc
    rw [hmin] at hSL' hhh
    have hm1 : (1:ℝ) ≤ ((N - T.j : ℕ) : ℝ) := by
      have : 1 ≤ N - T.j := by omega
      exact_mod_cast this
    set m : ℝ := ((N - T.j : ℕ) : ℝ) with hmdef
    have hSh : ∑ σ : Ψ, Sh (N := N) T.j σ (testPoly T.j) = 0 := Finset.sum_eq_zero (fun σ _ => (hs σ).1)
    have hTot : ∑ σ : Ψ, Tot (N := N) σ (testPoly T.j) = f * ((D + 1) * td * m) := by
      rw [Finset.sum_congr rfl (fun σ _ => (hs σ).2), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    rw [hPP, hSh, hTot] at hSL'
    have h1 : -(C * f * m * Λ) * ((D + 1) * td) ≤
        hh (testPoly T.j) - b₀ * (f * ((D + 1) * td * m)) + R := by
      refine le_of_mul_le_mul_left ?_ hvol
      calc T.volT * (-(C * f * m * Λ) * ((D + 1) * td))
          = -(C * f * m * Λ) * ((D + 1) * (T.volT * td)) := by ring
        _ ≤ _ := hSL'
        _ = T.volT * (hh (testPoly T.j) - b₀ * (f * ((D + 1) * td * m)) + R) := by ring
    have hb := lower_bound_key_inequality ((D + 1) * td) f m b₀ Λ C (hh (testPoly T.j)) R hK hf hm1 h1 l hhh hR
    have hj0 : (0:ℝ) < (T.j : ℝ) := by
      have : 0 < T.j := by omega
      exact_mod_cast this
    have hNj : (N:ℝ) ≤ 2 * (T.j : ℝ) := by
      have : N ≤ 2 * T.j := by omega
      exact_mod_cast this
    refine lower_bound_finite_arith (N:ℝ) (T.j:ℝ) A₀ _ hj0 hM0 hNj ?_
    have hNb := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) N)
    nlinarith
  · have hs := hcase2 hc
    have hmin : min T.j (N - T.j) = T.j := min_eq_left (by omega)
    rw [hmin] at hSL' hhh
    have hm1 : (1:ℝ) ≤ (T.j : ℝ) := by exact_mod_cast hj1
    set m : ℝ := (T.j : ℝ) with hmdef
    have hSh : ∑ σ : Ψ, Sh (N := N) T.j σ (testPoly T.j) = f * (-((D + 1) * m * td)) := by
      rw [Finset.sum_congr rfl (fun σ _ => (hs σ).1), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    have hTot : ∑ σ : Ψ, Tot (N := N) σ (testPoly T.j) = f * (-((D + 1) * m * td)) := by
      rw [Finset.sum_congr rfl (fun σ _ => (hs σ).2), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [hPP, hSh, hTot] at hSL'
    have h1 : -(C * f * m * Λ) * ((D + 1) * td) ≤
        hh (testPoly T.j) - (-(A₀ + b₀)) * (f * ((D + 1) * td * m)) + R := by
      refine le_of_mul_le_mul_left ?_ hvol
      calc T.volT * (-(C * f * m * Λ) * ((D + 1) * td))
          = -(C * f * m * Λ) * ((D + 1) * (T.volT * td)) := by ring
        _ ≤ _ := hSL'
        _ = T.volT * (hh (testPoly T.j) - (-(A₀ + b₀)) * (f * ((D + 1) * td * m)) + R) := by ring
    have hb := lower_bound_key_inequality ((D + 1) * td) f m (-(A₀ + b₀)) Λ C (hh (testPoly T.j)) R hK hf hm1 h1 l hhh hR
    have hcast : ((N - T.j : ℕ) : ℝ) = (N:ℝ) - (T.j:ℝ) := by
      rw [Nat.cast_sub (by omega)]
    have hpos : (0:ℝ) < ((N - T.j : ℕ) : ℝ) := by
      have : 0 < N - T.j := by omega
      exact_mod_cast this
    have hNj : (N:ℝ) ≤ 2 * ((N - T.j : ℕ) : ℝ) := by
      have : N ≤ 2 * (N - T.j) := by omega
      exact_mod_cast this
    refine lower_bound_finite_arith (N:ℝ) ((N - T.j : ℕ) : ℝ) A₀ _ hpos hM0 hNj ?_
    rw [hcast]
    have hNb := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) N)
    nlinarith

end GlobalTheory.CompanionTheory.Ar.Top
end

end

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.test_height_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd → T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C' rd Lval → T.SlopeLower II C rd Lval → hh (testPoly T.j) ≤ ((dimX Ψ N T.j : ℝ) + 1) * testDeg Ψ N T.j * (Fintype.card Ψ * ((min T.j (N - T.j) : ℕ) / 2 * Real.log (N + 1))) → T.LowerBoundAtBase II hh frob (2 * (C + C') + 3) rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.test_height_bound_slope_flat | exact GlobalTheory.CompanionTheory.Ar.Top.test_height_bound_slope_flat | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.test_height_bound_slope_flat <;> assumption)

end
end
