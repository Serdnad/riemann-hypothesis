module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlLeParams
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle100
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle201
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle202
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle091
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle095
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShapeRows

theorem ent_nu {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.nu u j z = nuD D u j z := by
  apply YoungDiagram.ext
  ext ⟨r, c⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen]
  have h : (E.nu u j z).rowLen r = (nuD D u j z).rowLen r := by
    have h1 := E.nu_row u j hj z r
    have h2 := nuRowOK D u j hj z r
    exact_mod_cast h1.trans h2.symm
  rw [h]

theorem ent_size {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.size u j z = (((nuD D u j z).card : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.size
  rw [ent_nu E u j hj z]

theorem ent_row {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) :
    E.row u j z r = (((nuD D u j z).rowLen r : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.row
  rw [ent_nu E u j hj z]

theorem ent_cap {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.cap u j z = if IsTopPl D z then (((nuD D u j z).rowLen 1 : ℕ) : ℝ) else (((nuD D u j z).rowLen 0 : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.cap
  rw [ent_row E u j hj z, ent_row E u j hj z]

theorem cap_le_width : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.LongRows.longRows Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  obtain ⟨-, hw, -⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 i j hj z
  have hr := h2 x (le_trans (le_max_right _ _) hx) hx1 i u j hj z
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    have := (Fm.D x i).R.two_le_m
    omega
  have hN : (Fm.D x i).R.k ≤ (Fm.D x i).R.N j := by unfold Ranks.N; omega
  have hS := (Fm.L x i).Sc_pos
  split_ifs with hz
  · have e := nuRowOK (Fm.D x i) u j hj z 1
    rw [if_pos (by omega)] at e
    have := ((hr 1 (by omega)).2 hz le_rfl (by omega)).2
    rw [e]
    linarith
  · have e := nuRowOK (Fm.D x i) u j hj z 0
    rw [if_pos (by omega)] at e
    have := ((hr 0 (by omega)).1 hz).2
    rw [if_pos rfl] at this
    rw [e]
    linarith

theorem shape : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (Ee : OrbitPlaces.Ent (Fm.D x i)), OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Ee := by
  intro eps Fm
  obtain ⟨a1, h1⟩ := GlobalTheory.Ggeo.wPl_pos Fm
  obtain ⟨a2, h2⟩ := GlobalTheory.ExcessLow.excess_mem_Icc Fm
  obtain ⟨a3, h3⟩ := GlobalTheory.TopExcess.top_excess Fm
  obtain ⟨a4, h4⟩ := GlobalTheory.TopFirstRow.two_w_le_first_row Fm
  obtain ⟨a5, h5⟩ := GlobalTheory.nuD_card_le_a_sq Fm
  obtain ⟨a6, h6⟩ := GlobalTheory.rank_two_logb_five_sq_le Fm
  obtain ⟨a7, h7⟩ := GlobalTheory.ShXa.X''_le_a Fm
  obtain ⟨a8, h8⟩ := GlobalTheory.family_one_lt_scale_a Fm
  obtain ⟨a9, h9⟩ := cap_le_width Fm
  obtain ⟨a10, h10⟩ := GlobalTheory.AlTop.al_le Fm
  obtain ⟨a11, h11⟩ := GlobalTheory.CapBound.cap_le Fm
  refine ⟨max a1 (max a2 (max a3 (max a4 (max a5 (max a6 (max a7 (max a8 (max a9 (max a10 a11))))))))),
    fun x hx hx1 i Ee => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hx
  exact
    { wpos := h1 x b1 hx1 i
      low := fun u j hj z hz => by
        rw [ent_size Ee u j hj z]
        exact h2 x b2 hx1 i u j hj z hz
      top := fun u j hj z hz => by
        rw [ent_size Ee u j hj z, ent_row Ee u j hj z]
        exact h3 x b3 hx1 i u j hj z hz
      top1 := fun u j hj z hz => by
        rw [ent_row Ee u j hj z]
        exact h4 x b4 hx1 i u j hj z hz
      sizeA := fun u j hj z => by
        rw [ent_size Ee u j hj z]
        exact h5 x b5 hx1 i u j hj z
      rankA := h6 x b6 hx1 i
      xa := ⟨h7 x b7 hx1 i, h8 x b8 hx1 i⟩
      capW := fun u j hj z => by
        rw [ent_cap Ee u j hj z]
        exact h9 x b9 hx1 i u j hj z
      alG := fun u j hj t ht => by
        rw [ent_row Ee u j hj, ent_row Ee u j hj]
        exact h10 x b10 hx1 i u j hj t ht
      capG := fun u j hj z => by
        rw [ent_cap Ee u j hj z]
        exact h11 x b11 hx1 i u j hj z }

end GlobalTheory.ShapeRows
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.IntStruct


open MvPolynomial in
theorem exists_coord_eq_sum_coeff {σ : Type} {d : ℕ} (V : Submodule ℂ (MvPolynomial σ ℂ)) (B : Module.Basis (Fin d) ℂ V)
    (i : Fin d) : ∃ (s : Finset (σ →₀ ℕ)) (a : s → ℂ), ∀ v : V,
      B.repr v i = ∑ m : s, a m * (v : MvPolynomial σ ℂ).coeff m.1 := by
  classical
  let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun j => ((B j : V) : MvPolynomial σ ℂ).support
  let R : V →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun m => (lcoeff ℂ m.1).comp V.subtype
  have hR : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    have h0 : ∀ m : s, (v : MvPolynomial σ ℂ).coeff m.1 = 0 := fun m => congrFun hv m
    refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
    change (v : MvPolynomial σ ℂ).coeff m = 0
    by_cases hm : m ∈ s
    · exact h0 ⟨m, hm⟩
    · have hv' : (v : MvPolynomial σ ℂ) = ∑ j, B.repr v j • ((B j : V) : MvPolynomial σ ℂ) := by
        calc (v : MvPolynomial σ ℂ) = ((∑ j, B.repr v j • B j : V) : MvPolynomial σ ℂ) := by rw [B.sum_repr v]
          _ = _ := by rw [Submodule.coe_sum]; rfl
      rw [hv', coeff_sum]
      simp only [MvPolynomial.coeff_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : m ∉ ((B j : V) : MvPolynomial σ ℂ).support := fun h =>
        hm (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩)
      rw [notMem_support_iff.1 this, smul_zero]
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
  refine ⟨s, fun m => B.repr (L (Pi.single m 1)) i, fun v => ?_⟩
  have e1 : B.repr v i = ((B.coord i).comp L) (R v) := by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply L R, hL, LinearMap.id_apply, Module.Basis.coord_apply]
  rw [e1, LinearMap.pi_apply_eq_sum_univ ((B.coord i).comp L) (R v)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hs : (fun j => if m = j then (1 : ℂ) else 0) = Pi.single m 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hs, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.IntStruct

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section
namespace GlobalTheory.CongEx

open UpperTheory.V.Af

theorem exists_place_over (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have hp : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Int.prime_iff_natAbs_prime.2 (by simpa using (Fact.out : l.Prime))).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(l : ℤ)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := by exact_mod_cast (algebraMap ℤ (𝓞 E)).injective_int (hx.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) _ hker
  have hl : ((l : ℕ) : 𝓞 E) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h => ?_⟩, hl⟩
  rw [h] at hQc
  have h0 : (l : ℤ) ∈ Ideal.span {(l : ℤ)} := Ideal.mem_span_singleton_self _
  rw [← hQc] at h0
  change (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) ⊥ at h0
  rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 E)).injective_int] at h0
  have := (Fact.out : l.Prime).ne_zero
  simp_all

theorem eventually_not_mem_l (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

end GlobalTheory.CongEx

end
end
