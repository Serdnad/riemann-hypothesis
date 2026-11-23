module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantJensenChangeOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniform
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1686
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N 0 R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f :=
    fun a c σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hpH, hpn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t htH N
  have e1 : (N : ℤ) + N * -1 = 0 := by ring
  have e2 : (0 : ℤ) + N * b = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N 0 R, f * t ^ N ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 (N * -1) (N * b) f (t ^ N) hfH hpH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hpn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    exact (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
  have hinj : Set.InjOn (fun f => f * t ^ N) (P.Bl N 0 R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) h
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N 0 R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hX P b s t hG
  have hRep : P.Rep 0 (b : ℤ) (P.A.pow b) := by
    have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A b (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
    simpa using this
  have hnef : (P.A.pow b).IsNef D := GlobalTheory.T.isNef_pow_of_isNef hAC k X p D hX P.A b hG.nef
  have hnef0 : ((P.A.pow b).shift (fun _ => (0 : ℝ)) fun _ => rfl).IsNef D :=
    GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX (P.A.pow b) 0 le_rfl hnef
  obtain ⟨Φ, hΦ⟩ := ((hAC.arExists k X p D hX).2 Unit (fun _ => P.A.pow b)).1
  have hα := ((hAC.arIso k X p D hX).2 Unit (fun _ => P.A.pow b) Φ hΦ).1 ()
  have hlim := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hAC k X p D hX P 0 b (P.A.pow b) _ 0 hRep hα hnef0 3 (by norm_num)
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      P.lc ((m : ℤ) * 0) ((m : ℤ) * b) (Real.exp (3 * m)) / (m : ℝ) ^ (D + 1) < C :=
    ⟨_, hlim.eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  rw [div_lt_iff₀ hpos] at hN
  simp only [mul_zero] at hN
  refine le_trans ?_ hN.le
  exact lc_le_of_good P hG N _ (GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 _ _ hAC)

end GlobalTheory.VolBr
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → IsFam (fun σ => (ω σ).meas) (vals P a b f) ∧ (gram (fun σ => (ω σ).meas) (vals P a b f)).PosDef ∧ ∀ (c : ι → ℂ) (M : ℝ), (∀ σ y, cmb (vals P a b f) c σ y ≤ M) → l2 (fun σ => (ω σ).meas) (vals P a b f) c ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * M := by
  first | exact @GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound | exact GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound | (intros; apply GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

theorem _root_.GlobalTheory.T.gramDeterminant_jensen_change_of_weight : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → ∀ (w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Measurable (w σ)) → (∀ σ y, |w σ y| ≤ C) → IsFam μ (fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)) ∧ (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).PosDef ∧ Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤ Real.log (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).det.re := by
  first | exact @GlobalTheory.GramJensen.gram_det_jensen | exact GlobalTheory.GramJensen.gram_det_jensen | (intros; apply GlobalTheory.GramJensen.gram_det_jensen <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (ρ : ∀ σ, CxPts p σ → ℝ), (∀ σ, (ω σ).IsRatio (P.L.φ σ) (ρ σ)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ (ι : Type) [Fintype ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ) (σ : k →+* ℂ) (y : CxPts p σ), cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  first | exact @GlobalTheory.HSAmp.Morse.cmb_le | exact GlobalTheory.HSAmp.Morse.cmb_le | (intros; apply GlobalTheory.HSAmp.Morse.cmb_le <;> assumption)
end

section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_archimedeanPhaseSpace_complexStructure_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.HoweD.exists_bridgeD | exact GlobalTheory.HoweD.exists_bridgeD | (intros; apply GlobalTheory.HoweD.exists_bridgeD <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.genericallyFinite_finite_near_codimOne_point : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ z : X, Order.coheight z = 1 → (g ⁻¹' {z}).Finite ∧ (∀ w : Y, g w = z → Order.coheight w = 1) ∧ ∃ V : X.Opens, IsAffineOpen V ∧ z ∈ V ∧ IsFinite (g ∣_ V) := by
  first | exact @GlobalTheory.PushFinite.finite_near_coheight_one | exact GlobalTheory.PushFinite.finite_near_coheight_one | (intros; apply GlobalTheory.PushFinite.finite_near_coheight_one <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.isGoodGlRep_piTensorActionAtFactor_and_commute : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)), (∀ w, Good (a w)) → (∀ w, Good (actAt w (a w))) ∧ ∀ w w', w ≠ w' → ∀ Z Z' v, actAt w (a w) Z (actAt w' (a w') Z' v) = actAt w' (a w') Z' (actAt w (a w) Z v) := by
  first | exact @GlobalTheory.HoweR.actAt_good_comm | exact GlobalTheory.HoweR.actAt_good_comm | (intros; apply GlobalTheory.HoweR.actAt_good_comm <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ T, IsMix q e T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → recVal (T e L) L M hr = recVal (T e L') L' M hr) ∧ (∀ (L : Fin e → HermLB q) (τ : Equiv.Perm (Fin e)), recVal (T e fun a => L (τ a)) (fun a => L (τ a)) M hr = recVal (T e L) L M hr) ∧ (∀ (L : Fin e → HermLB q) (M' : HermLB q), M.Isometric M' → ∃ (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), recVal (T e L) L M' hr' = recVal (T e L) L M hr) := by
  first | exact @GlobalTheory.MixHt.recVal_iso_symm | exact GlobalTheory.MixHt.recVal_iso_symm | (intros; apply GlobalTheory.MixHt.recVal_iso_symm <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.exists_unitary_piece_bounded_weights_of_quadratic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β α' β' : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), Nontrivial M → IsGl F → (∀ a b, qop F α β a b = 0) → (∀ a b, qop (negT F) α' β' a b = 0) → LocU s F → ∃ U : Submodule ℂ M, U ≠ ⊥ ∧ UnitOn s F U ∧ ∀ a, ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → |m.re| ≤ R := by
  first | exact @GlobalTheory.HoweR.exists_unitOn_diag_bounded | exact GlobalTheory.HoweR.exists_unitOn_diag_bounded | (intros; apply GlobalTheory.HoweR.exists_unitOn_diag_bounded <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.SympFramesD

theorem symp_framesD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : InfinitePlace F → ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  intro F E _ _ _ _ _ σ α β _ _ _ _ P Q R S τ JA JB a b A C hCM hF u u' c c' _ _ hu hu'
  have key : ∀ w, a * b * piInf (τ w) (hTens (cA σ) JA JB u u') =
      ∑ x, ∑ y, lineSign x y * c w x y * star (c' w x y) := by
    intro w
    have e : piInf (τ w) (hTens (cA σ) JA JB u u') = ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf (τ w)) i j *
        JA.map (piInf (τ w)) i k * JB.map (piInf (τ w)) j l * star (u'.map (piInf (τ w)) k l) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hTens, map_sum, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, Matrix.map_apply]
    rw [e, hu w, hu' w, GlobalTheory.SympFrames.quad_eq_trace]
    exact GlobalTheory.SympFrames.frame_trace _ _ a b (A w) (C w) (hF.2.1 w).1 (hF.2.2 w).1 (c w) (c' w)
  rw [symp, GlobalTheory.WrongSignPair.trace_evI_trace hCM τ, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 := key w
  rw [hF.1] at h2
  rw [← h2, map_mul, map_neg, map_one]
  simp only [Complex.neg_re, Complex.mul_im, Complex.I_re, Complex.I_im, neg_one_mul, zero_mul, one_mul, zero_add]
  ring

end GlobalTheory.SympFramesD
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.finsum_mult_resCyc_indicator_symm' : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ x : Y, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
  first | exact @GlobalTheory.MixHt.finsum_mult_resCyc_indicator_symm | exact GlobalTheory.MixHt.finsum_mult_resCyc_indicator_symm | (intros; apply GlobalTheory.MixHt.finsum_mult_resCyc_indicator_symm <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_local_conj_trivialization_at_place_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (g : G.GAf) (c Y : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * Y * ((c⁻¹ : G.Cˣ) : G.C) → ∀ w : AwayP p,
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
        inC G (w.1.adicCompletion ℚ) (β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  first | (exact @GlobalTheory.FinClsLoc.glueL_main) | (exact GlobalTheory.FinClsLoc.glueL_main) | (intros; apply GlobalTheory.FinClsLoc.glueL_main  <;> assumption)
end
