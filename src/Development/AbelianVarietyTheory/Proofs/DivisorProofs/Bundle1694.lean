module

public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
public import Formalism.UnipotentAdelicQuotients.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelFiniteClassNumberCentraliserTorus
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeSize

variable {D : D7}

theorem card_TT_le (D : D7) : (D.host.TT.card : ℝ) ≤ D.R.f := by
  have h : Fintype.card D.host.TT ≤ Fintype.card D.what₂.Tau := by
    refine Fintype.card_le_of_injective
      (fun t => D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) ?_
    intro a b hab
    have h1 := congrArg Subtype.val (D.eTau.symm.injective hab)
    exact Subtype.ext (GlobalTheory.FockDegreeGap.tau1_injective h1)
  rw [Fintype.card_coe, D.what₂.card_Tau] at h
  exact_mod_cast h

theorem errG_abs_le {L : SizeData₂ D} (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (C : ℝ) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) : |WeightDegreeSizes.errG L C j| ≤ (6 + 4 * |C|) * D.R.f * L.sc.b := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨e1, e2, e3⟩ := GlobalTheory.FockDegreeGap.errors_le h P
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hb' := GlobalTheory.HCEntries.b'_pos L
  have hbb : L.sc.b' ≤ L.sc.b := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    linarith [GlobalTheory.HCEntries.b'_Sc_le hS, L.Sc_pos]
  have hx0 : 0 < L.sc.x := by linarith
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b := (div_le_self hb'.le (by linarith)).trans hbb
  have hTT := card_TT_le D
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hTT0 : (0 : ℝ) ≤ D.host.TT.card := Nat.cast_nonneg _
  have hw0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ :=
    Finset.sum_nonneg fun τ _ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).1
  have hw1 : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => wj D j τ) (3 * L.sc.b)
      (fun τ _ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).2)
    rwa [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at this
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hN0 : (0 : ℝ) ≤ Formalism.MainNotions.G.Nm D := by unfold Formalism.MainNotions.G.Nm; positivity
  have hmt : (D.R.m : ℝ) * D.R.t * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    have : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    nlinarith
  have hkN : (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D ≤ L.sc.b := e3
  set Y : ℝ := (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D) +
    (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x with hY
  have hY0 : 0 ≤ Y := by
    rw [hY]
    have : 0 ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by positivity
    have : 0 ≤ (D.R.k : ℝ) * L.Sc := by positivity
    have : 0 ≤ (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D := by positivity
    have : 0 ≤ (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x := by positivity
    positivity
  have hY1 : Y ≤ 4 * D.R.f * L.sc.b := by
    rw [hY, mul_div_assoc]
    have a1 : (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D) ≤
        D.R.f * (3 * L.sc.b) := mul_le_mul_of_nonneg_left (by linarith) hf0
    have a2 : (D.host.TT.card : ℝ) * (L.sc.b' / L.sc.x) ≤ D.R.f * L.sc.b :=
      mul_le_mul hTT hbx (by positivity) hf0
    linarith
  have hCY : |C * Y| ≤ 4 * |C| * D.R.f * L.sc.b := by
    rw [abs_mul, abs_of_nonneg hY0]
    calc |C| * Y ≤ |C| * (4 * D.R.f * L.sc.b) := mul_le_mul_of_nonneg_left hY1 (abs_nonneg _)
      _ = _ := by ring
  have e : WeightDegreeSizes.errG L C j = 2 * (∑ τ : D.what₂.Tau, wj D j τ) + C * Y := by
    unfold WeightDegreeSizes.errG; rw [hY]
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (∑ τ : D.what₂.Tau, wj D j τ))]
  nlinarith

theorem typePrime_sizes_le_budget_single {L : SizeData₂ D} (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (c : ErrC) (Cd C₂ : ℝ)
    (h2 : FactDGam D C₂) :
    WeightDegreeSizes.TypePrimeSizeBound D L c Cd (|(6 + 4 * |Cd|)| * (P.CYL + 1) + 2 * |C₂| + 4 * |c.g| * (P.CYL + 1)) := by
  intro i u j hj
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by exact_mod_cast hmfn
  have hf : (1 : ℝ) ≤ D.R.f := hm.trans hmf
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hfη : (D.R.f : ℝ) * L.etaSz ≤ L.sc.b := by
    have a1 := P.eta_le
    rw [le_div_iff₀ (by positivity)] at a1
    have a2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (one_le_pow₀ hk)
    have a3 : (D.R.f : ℝ) * L.etaSz ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3) :=
      le_mul_of_one_le_right (by positivity) a2
    calc _ ≤ _ := a3
      _ = L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by ring
      _ ≤ _ := a1
  have hg0 : (0 : ℝ) < D.host.g i := by exact_mod_cast (D.host.g_prime i).pos
  have hlg0 : 0 ≤ Real.log (D.host.g i) := Real.log_natCast_nonneg _
  have hlg : Real.log (D.host.g i) ≤ (P.CYL + 1) * L.sc.L := by
    obtain ⟨Y, -, -, hY, hg⟩ := P.g_Y
    have hY0 : 0 < Y := by linarith [(hg i).2]
    have a1 : Real.log (D.host.g i) ≤ Real.log (2 * Y) := Real.log_le_log hg0 (hg i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at a1
    have a2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have key := GlobalTheory.TypeLoss.arith_bound (WeightDegreeSizes.errG L Cd j)
    ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) _ (Real.log (D.host.g i))
    D.R.f D.R.m L.sc.b L.sc.L (D.R.N D.R.m) L.etaSz (6 + 4 * |Cd|) C₂ c.g P.CYL L.B0 rfl hf hm hL hN P.CYL_pos.le
    (errG_abs_le h P hx Cd j hj)
    (mul_nonneg (Nat.cast_nonneg _) hlg0)
    ((GlobalTheory.TypeLoss.padic_log_le _ _ (D.host.g_prime i)).trans (h2 u)) rfl hlg0 hlg hη0 hNη hmf hfη
  have e : (WeightDegreeSizes.errG L Cd j + 2 * (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) +
      2 * (c.g * (D.R.f : ℝ) * (Formalism.MainNotions.G.Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz))) * Real.log (D.host.g i : ℝ) =
      WeightDegreeSizes.errG L Cd j * Real.log (D.host.g i) +
        2 * ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) +
        2 * (c.g * (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)) * Real.log (D.host.g i) := by
    unfold Formalism.MainNotions.G.Nm; ring
  rw [e]
  exact (le_abs_self _).trans key

theorem typePrimeSizeBound_of_eps_lt_one_div_fiftyTwo : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → DGamSize Fm → ∀ Cd : ℝ, ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err Cd C := by
  intro eps Fm _ _ ⟨C₂, x₂, h2⟩ Cd
  refine ⟨max (|(6 + 4 * |Cd|)| * (Fm.CYL + 1) + 2 * |C₂| + 4 * |Fm.cX.err.g| * (Fm.CYL + 1)) 0, max 2 x₂,
    le_max_right _ _, ?_⟩
  · intro x hx0 hx i
    have a := typePrime_sizes_le_budget_single (Fm.sizes x hx i) (Fm.params x hx i)
      (by rw [Fm.L_x x i hx]; exact (le_max_left _ _).trans hx0) Fm.cX.err Cd C₂
      (h2 x ((le_max_right _ _).trans hx0) i)
    rw [Fm.params_CYL x hx i] at a
    intro k u j hj
    exact (a k u j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (WeightDegreeSizes.loss_bound_nonneg _))

end GlobalTheory.TypeSize

end
end

section

open GlobalTheory.LKTrip
open scoped TensorProduct

theorem _root_.GlobalTheory.T.borel_finite_classNumber_centraliserTorus : (∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R))) → HeckeCharacterZeroLocus.ClassNumberFinite → ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime],
    letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
    ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
      (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
        ∀ z ∈ O, GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) →
      ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
        ∀ z, GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 →
          ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ γ.1).unop = algebraMap ℚ D γ.2 * β ∧ Commute (γ.1 : D) y ∧
            ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u := by
  first | (exact @GlobalTheory.TorCls.Borel.classes_finite) | (exact GlobalTheory.TorCls.Borel.classes_finite) | (intros; apply GlobalTheory.TorCls.Borel.classes_finite  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory

theorem twisted_norm_local_step : ∀ {A K : Type} [Ring A] [CommRing K] [Algebra K A] (σ : A →+* Aᵐᵒᵖ), (∀ x, (σ (σ x).unop).unop = x) →
    ∀ (β Y k z m : Aˣ) (a : A) (lam s : Kˣ), (σ (β : A)).unop = β →
    (Y : A) * β * (σ (Y : A)).unop = algebraMap K A s * β → Commute a Y →
    (k : A) * (a * β) * (σ (k : A)).unop = algebraMap K A lam → k⁻¹ = z * m → Commute (z : A) Y →
    (∀ m' : Aˣ, (m' : A) = m * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) → Commute (m' : A) Y →
      (β : A) * (σ (m' : A)).unop * ((β⁻¹ : Aˣ) : A) = m' →
      ∃ v : Aˣ, Commute (v : A) Y ∧ (m' : A) = v * ((β : A) * (σ (v : A)).unop * ((β⁻¹ : Aˣ) : A))) →
    ∃ z' : Aˣ, Commute (z' : A) Y ∧ a = algebraMap K A lam * ((z' : A) * β * (σ (z' : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
  intro A K _ _ _ σ hσ β Y k z m a lam s hβ hY haY hk hkz hzY H
  have shmul : ∀ x y : A, (σ (x * y)).unop = (σ y).unop * (σ x).unop := fun x y => by
    rw [map_mul, MulOpposite.unop_mul]
  have shinv : ∀ u : Aˣ, (σ ((u⁻¹ : Aˣ) : A)).unop * (σ (u : A)).unop = 1 := fun u => by
    rw [← shmul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have shinv' : ∀ u : Aˣ, (σ (u : A)).unop * (σ ((u⁻¹ : Aˣ) : A)).unop = 1 := fun u => by
    rw [← shmul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have shc : ∀ (u : Aˣ) (x : A), (σ (u : A)).unop * ((σ ((u⁻¹ : Aˣ) : A)).unop * x) = x := by
    intro u x; rw [← mul_assoc, shinv', one_mul]

  have hτY : (β : A) * (σ (Y : A)).unop * ((β⁻¹ : Aˣ) : A) = algebraMap K A s * ((Y⁻¹ : Aˣ) : A) := by
    have h := congrArg (fun x => ((Y⁻¹ : Aˣ) : A) * x * ((β⁻¹ : Aˣ) : A)) hY
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one] at h
    rw [mul_assoc, h]
    exact (Algebra.commutes _ _).symm
  have hτ : ∀ w : A, Commute w Y → Commute ((β : A) * (σ w).unop * ((β⁻¹ : Aˣ) : A)) Y := by
    intro w hw
    have hsh : Commute (σ w).unop (σ (Y : A)).unop := by
      show _ = _
      rw [← shmul, ← shmul, hw.eq]
    have hc : Commute ((β : A) * (σ w).unop * ((β⁻¹ : Aˣ) : A))
        ((β : A) * (σ (Y : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
      show _ = _
      simp only [mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc (σ w).unop, hsh.eq, mul_assoc]
    rw [hτY] at hc
    have h2 := (Algebra.commute_algebraMap_right ((s⁻¹ : Kˣ) : K) _).mul_right hc
    rw [← mul_assoc (algebraMap K A ((s⁻¹ : Kˣ) : K)), ← map_mul, Units.inv_mul, map_one,
      one_mul] at h2
    exact Commute.units_inv_right_iff.mp h2

  have e : a * (β : A) = ((k⁻¹ : Aˣ) : A) * ((k : A) * (a * β) * (σ (k : A)).unop) *
      (σ ((k⁻¹ : Aˣ) : A)).unop := by
    simp only [mul_assoc, shinv', shc, mul_one, Units.inv_mul_cancel_left]
  rw [hk, ← Algebra.commutes (lam : K), hkz, Units.val_mul, shmul] at e
  have ha : a = algebraMap K A lam * ((z : A) * ((m : A) * (σ (m : A)).unop) * (σ (z : A)).unop *
      ((β⁻¹ : Aˣ) : A)) := by
    calc a = a * β * ((β⁻¹ : Aˣ) : A) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [e]; simp only [mul_assoc]

  have hbi : (σ ((β⁻¹ : Aˣ) : A)).unop = ((β⁻¹ : Aˣ) : A) := by
    have h := shinv β
    rw [hβ] at h
    calc (σ ((β⁻¹ : Aˣ) : A)).unop = (σ ((β⁻¹ : Aˣ) : A)).unop * β * ((β⁻¹ : Aˣ) : A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h, one_mul]
  let mu : Aˣ := ⟨(σ (m : A)).unop, (σ ((m⁻¹ : Aˣ) : A)).unop, shinv' m, shinv m⟩
  let m' : Aˣ := m * mu * β⁻¹
  have hm' : (m' : A) = m * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) := rfl
  have hm'c : (m' : A) = ((z⁻¹ : Aˣ) : A) * (algebraMap K A ((lam⁻¹ : Kˣ) : K) * a) *
      ((β : A) * (σ ((z⁻¹ : Aˣ) : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
    rw [hm', ha, ← mul_assoc (algebraMap K A ((lam⁻¹ : Kˣ) : K)), ← map_mul, Units.inv_mul,
      map_one, one_mul]
    simp only [mul_assoc, Units.inv_mul_cancel_left, shc]
  have hmY : Commute (m' : A) Y := by
    rw [hm'c]
    exact ((hzY.units_inv_left).mul_left
      ((Algebra.commute_algebraMap_left _ _).mul_left haY)).mul_left (hτ _ hzY.units_inv_left)
  have hmτ : (β : A) * (σ (m' : A)).unop * ((β⁻¹ : Aˣ) : A) = m' := by
    rw [hm', shmul, shmul, hσ, hbi]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  obtain ⟨v, hvY, hv⟩ := H m' hm' hmY hmτ
  have h3 : (m : A) * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) =
      v * β * (σ (v : A)).unop * ((β⁻¹ : Aˣ) : A) := by
    rw [← hm', hv]; simp only [mul_assoc]
  have hmm := (Units.mul_left_inj β⁻¹).mp h3
  refine ⟨z * v, by rw [Units.val_mul]; exact hzY.mul_left hvY, ?_⟩
  rw [Units.val_mul, shmul, ha, hmm]
  simp only [mul_assoc]

end GlobalTheory
end

section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.RealPartDet

open Matrix

theorem quad_eq_sum {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ G *ᵥ c = ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * G i j := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem quad_transpose_eq_sum {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ Gᵀ *ᵥ c = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * G i j := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem map_re_map_ofReal {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian) :
    (G.map Complex.re).map (fun r : ℝ => (r : ℂ)) = (2 : ℂ)⁻¹ • (G + Gᵀ) := by
  ext i j
  have h := hG.apply j i
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, transpose_apply, smul_eq_mul, ← h,
    Complex.star_def, Complex.re_eq_add_conj]
  ring

theorem quad_half_re {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ) (c : ι → ℂ) :
    (star c ⬝ᵥ ((2 : ℂ)⁻¹ • (G + Gᵀ)) *ᵥ c).re
      = ((star c ⬝ᵥ G *ᵥ c).re + (star c ⬝ᵥ Gᵀ *ᵥ c).re) / 2 := by
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec, dotProduct_add, smul_eq_mul]
  simp [Complex.mul_re]
  ring

theorem quad_ofReal {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    star (fun i => (x i : ℂ)) ⬝ᵥ (A.map (fun r : ℝ => (r : ℂ))) *ᵥ (fun i => (x i : ℂ))
      = ((x ⬝ᵥ A *ᵥ x : ℝ) : ℂ) := by
  simp [dotProduct, mulVec, Complex.ofReal_sum, Complex.ofReal_mul]

theorem main : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (κ : ℝ), G.PosDef → 1 ≤ κ →
    (∀ c : ι → ℂ, (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * G i j).re ≤
      κ * (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * G i j).re) →
    (G.map Complex.re).PosDef ∧
      |Real.log (G.map Complex.re).det - Real.log G.det.re| ≤ Fintype.card ι * Real.log (2 * κ) := by
  intro ι _ _ G κ hG hκ h
  set A := G.map Complex.re with hAdef
  set Ac := A.map (fun r : ℝ => (r : ℂ)) with hAcdef
  have hAc : Ac = (2 : ℂ)⁻¹ • (G + Gᵀ) := map_re_map_ofReal hG.isHermitian
  have h2 : (0 : ℂ) < (2 : ℂ)⁻¹ := by rw [Complex.pos_iff]; norm_num
  have hAcpd : Ac.PosDef := by rw [hAc]; exact (hG.add hG.transpose).smul h2

  have hq1 : ∀ c : ι → ℂ, (star c ⬝ᵥ G *ᵥ c).re ≤ κ * (star c ⬝ᵥ Gᵀ *ᵥ c).re := by
    intro c; rw [quad_eq_sum, quad_transpose_eq_sum]; exact h c
  have hq2 : ∀ c : ι → ℂ, (star c ⬝ᵥ Gᵀ *ᵥ c).re ≤ κ * (star c ⬝ᵥ G *ᵥ c).re := by
    intro c
    have := h (fun i => (starRingEnd ℂ) (c i))
    simp only [Complex.conj_conj] at this
    rw [quad_transpose_eq_sum, quad_eq_sum]
    exact this
  have hn1 : ∀ c : ι → ℂ, 0 ≤ (star c ⬝ᵥ G *ᵥ c).re := fun c =>
    (Complex.nonneg_iff.1 (hG.posSemidef.dotProduct_mulVec_nonneg c)).1
  have hn2 : ∀ c : ι → ℂ, 0 ≤ (star c ⬝ᵥ Gᵀ *ᵥ c).re := fun c =>
    (Complex.nonneg_iff.1 (hG.transpose.posSemidef.dotProduct_mulVec_nonneg c)).1
  have hqA : ∀ c : ι → ℂ, (star c ⬝ᵥ Ac *ᵥ c).re
      = ((star c ⬝ᵥ G *ᵥ c).re + (star c ⬝ᵥ Gᵀ *ᵥ c).re) / 2 := fun c => by
    rw [hAc]; exact quad_half_re G c

  have hApd : A.PosDef := by
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      have e := hG.isHermitian.apply i j
      simp only [conjTranspose_apply, star_trivial, hAdef, Matrix.map_apply]
      rw [← e, Complex.star_def, Complex.conj_re]
    · have hc : (fun i => (x i : ℂ)) ≠ 0 := by
        intro h0; apply hx; funext i
        have := congrFun h0 i
        simpa using this
      have := (posDef_iff_dotProduct_mulVec.1 hAcpd).2 hc
      rw [quad_ofReal] at this
      simpa [star_trivial] using (Complex.zero_lt_real.1 this)
  refine ⟨hApd, ?_⟩

  have hdet : Ac.det.re = A.det := by
    have := (Complex.ofRealHom.map_det A)
    rw [hAcdef]
    rw [show A.map (fun r : ℝ => (r : ℂ)) = Complex.ofRealHom.mapMatrix A from rfl, ← this]
    simp
  have d1 : G.det.re ≤ 2 ^ Fintype.card ι * A.det := by
    rw [← hdet]
    refine GlobalTheory.T.det_re_le_pow_mul_det_re_of_posDef ι G Ac 2 hG hAcpd fun c => ?_
    rw [hqA c]; linarith [hn2 c]
  have d2 : A.det ≤ κ ^ Fintype.card ι * G.det.re := by
    rw [← hdet]
    refine GlobalTheory.T.det_re_le_pow_mul_det_re_of_posDef ι Ac G κ hAcpd hG fun c => ?_
    rw [hqA c]; nlinarith [hq2 c, hn1 c]
  have ha : 0 < A.det := hApd.det_pos
  have hg : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have hκ0 : 0 < κ := by linarith
  have l1 : Real.log G.det.re ≤ Fintype.card ι * Real.log 2 + Real.log A.det := by
    have := Real.log_le_log hg d1
    rwa [Real.log_mul (by positivity) ha.ne', Real.log_pow] at this
  have l2 : Real.log A.det ≤ Fintype.card ι * Real.log κ + Real.log G.det.re := by
    have := Real.log_le_log ha d2
    rwa [Real.log_mul (by positivity) hg.ne', Real.log_pow] at this
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlk : 0 ≤ Real.log κ := Real.log_nonneg hκ
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rw [Real.log_mul (by norm_num) hκ0.ne', mul_add]
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [mul_nonneg hn hl2]
  · nlinarith [mul_nonneg hn hlk]

end GlobalTheory.RealPartDet
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.rapidDecay_smallestRatio_absorbs_height_and_character : ∀ (a : ℕ) (t : ℝ), 0 < t → ∀ (lam : Fin a → ℝ) (N : ℕ), ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i ∨ ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ (r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i := by
  first | exact @GlobalTheory.rapidDecay_real | exact GlobalTheory.rapidDecay_real | (intros; apply GlobalTheory.rapidDecay_real <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_isIso_of_mono_same_dimension : ∀ (S : Scheme.{0}) (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g B'.hom → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  first | exact @GlobalTheory.AbMonoIsoAny.isIso_of_mono | exact GlobalTheory.AbMonoIsoAny.isIso_of_mono | (intros; apply GlobalTheory.AbMonoIsoAny.isIso_of_mono <;> assumption)
end
