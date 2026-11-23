module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSAmp.GenMap

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem mem_chart {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
  Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))

theorem loc_mul_div (P : Pair p) (e : ℕ) (f ρ : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc e 0 f i j * (ρ / P.loc e 0 1 i j) = f * ρ := by
  have := (P.r i).ne_zero
  have := (P.r' j).ne_zero
  simp only [Pair.loc]
  field_simp

theorem loc_eq_mul_inv (P : Pair p) (e : ℕ) (f ρ : X.functionField) (hρ : ρ ≠ 0) (i : P.L.B.ι)
    (j : P.A.B.ι) : P.loc e 0 f i j = f * ρ * (ρ / P.loc e 0 1 i j)⁻¹ := by
  have := (P.r i).ne_zero
  have := (P.r' j).ne_zero
  simp only [Pair.loc]
  field_simp

theorem exists_secs (P : Pair p) {D e : ℕ} {x : Fin (D + 1) → X.functionField} (hx : Gens P D e x) :
    ∃ (ρ : (P.L.pow e).B.ι → X.functionFieldˣ) (s : Fin (D + 1) → (P.L.pow e).B.Sec),
      (∀ z c i j, z ∈ (P.L.pow e).B.U c → z ∈ P.L.B.U i → z ∈ P.A.B.U j →
        UnitAt z ((ρ c : X.functionField) / P.loc e 0 1 i j)) ∧
      (∀ (σ : k →+* ℂ) (y : CxPts p σ) c j, y ∈ ptsIn p σ ((P.L.pow e).B.U c) → y ∈ ptsIn p σ (P.A.B.U j) →
        ‖ratVal ((ρ c : X.functionField) / P.loc e 0 1 (c PUnit.unit) j) y‖ = 1) ∧
      ∀ l c (hc : genericPoint X ∈ (P.L.pow e).B.U c), fnOf _ hc ((s l).f c) = x l * ρ c := by
  obtain ⟨ρ, hρ, hu, hn⟩ := Pair.rep_pow k X p P 1 0 P.L e (Pair.rep_base k X p P).1
  simp only [mul_one, mul_zero] at hu hn
  have hs : ∀ l, ∃ u : (P.L.pow e).B.Sec, ∀ c (hc : genericPoint X ∈ (P.L.pow e).B.U c),
      fnOf _ hc (u.f c) = x l * ρ c := fun l =>
    RepDict.exists_sec hρ fun c z hz => by
      obtain ⟨i, hi⟩ := mem_chart P.L.isLB z
      obtain ⟨j, hj⟩ := mem_chart P.A.isLB z
      rw [← loc_mul_div P e (x l) _ i j]
      exact (hx.mem l z i j hi hj).mul (hu z c i j hz hi hj).regAt
  choose s hs using hs
  refine ⟨ρ, s, hu, fun σ y c j hc hj => ?_, hs⟩
  have hc' := mem_pow_iff.1 hc
  have hU := hu _ c _ j (mem_ptsIn.1 hc) (mem_ptsIn.1 hc') (mem_ptsIn.1 hj)
  have h1 := hn σ y c _ j hc hc' hj
  have h2 : ((P.L.pow e).φ σ).φ c y = ((e : ℤ) : ℝ) * (P.L.φ σ).φ (c PUnit.unit) y := Weight.zpow_φ _ _ _ _
  rw [h2] at h1
  push_cast at h1
  refine Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (ratVal_ne_zero hU)) ?_
  linarith

end GlobalTheory.HSAmp.GenMap

namespace GlobalTheory.HSAmp.GenMap

theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → x 0 ≠ 0 → ∃ (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D _ P e x hx hx0
  obtain ⟨ρ, s, hu, hn1, hs⟩ := exists_secs P hx
  have hnz : ∀ l z i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j →
      (z ∈ Out.nonzeroLocus (s l) ↔ UnitAt z (P.loc e 0 (x l) i j)) := by
    intro l z i j hi hj
    obtain ⟨c, hc⟩ := mem_chart (P.L.pow e).isLB z
    have hU := hu z c i j hc hi hj
    rw [mem_nonzeroLocus_iff (s l) c hc, ← unitAt_fnOf_iff hc (gen_mem hc), hs l c (gen_mem hc)]
    exact ⟨fun h => loc_eq_mul_inv P e (x l) _ (ρ c).ne_zero i j ▸ h.mul hU.inv,
      fun h => loc_mul_div P e (x l) _ i j ▸ h.mul hU⟩
  have hcov : ⨆ l, Out.nonzeroLocus (s l) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨i, hi⟩ := mem_chart P.L.isLB z
    obtain ⟨j, hj⟩ := mem_chart P.A.isLB z
    obtain ⟨l, hl⟩ := hx.cover z
    exact Opens.mem_iSup.2 ⟨l, (hnz l z i j hi hj).2 (hl i j hi hj)⟩
  obtain ⟨c, hc⟩ := mem_chart (P.L.pow e).isLB (genericPoint X)
  have hη : genericPoint X ∈ Out.nonzeroLocus (s 0) := by
    rw [mem_nonzeroLocus_iff (s 0) c hc, X.mem_basicOpen _ _ hc]
    show IsUnit (fnOf _ hc ((s 0).f c))
    rw [hs 0 c hc]
    exact isUnit_iff_ne_zero.2 (mul_ne_zero hx0 (ρ c).ne_zero)
  have hpre := ProjSpace.toProj_preimage_chart p s hcov 0
  have hmem : genericPoint X ∈ ProjSpace.toProj p s hcov ⁻¹ᵁ ProjSpace.chart k D 0 := by
    rw [hpre]; exact hη
  refine ⟨ProjSpace.toProj p s hcov, ProjSpace.toProj_str p s hcov, ⟨hmem, fun j => ?_⟩, fun u hu' => ?_⟩
  · change fnOf _ hmem _ = _
    rw [ProjSpace.pullRatio_toProj_on p s hcov 0 j le_rfl, fnOf_resG]
    have hc' : genericPoint X ∈ Out.nonzeroLocus (s 0) ⊓ (P.L.pow e).B.U c := ⟨hη, hc⟩
    have e1 := congrArg (fnOf _ hc') (ProjSpace.secRatio_spec (s 0) (s j) c)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hs j c hc, hs 0 c hc] at e1
    rw [eq_div_iff hx0]
    refine mul_right_cancel₀ (ρ c).ne_zero ?_
    linear_combination -e1
  · have he : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hx.pos.ne'
    refine (HermLB.isometric_pull_fs_toProj k X p ((up P.L u).pow e) D s hcov (fun _ => 1) (fun _ => by simp)
      (fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩) ?_).symm
    intro σ i y hy
    change y ∈ ptsIn p σ ((P.L.pow e).B.U i) at hy
    have hy' : y ∈ ptsIn p σ (P.L.B.U (i PUnit.unit)) := mem_pow_iff.1 hy
    have hj : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
    have hg := hn1 σ y i _ hy hj
    have hA : ∀ l, ‖valR y.1 ((P.L.pow e).B.U i) ((s l).f i)‖ =
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ := fun l => by
      have hη := gen_mem (mem_ptsIn.1 hy)
      change ‖ev p σ _ ((s l).f i) y‖ = _
      rw [← ratVal_fnOf hy hη, hs l i hη, ← loc_mul_div P e (x l) _ (i PUnit.unit) _,
        ratVal_mul (hx.mem l _ _ _ (mem_ptsIn.1 hy') (mem_ptsIn.1 hj))
          (hu _ i _ _ (mem_ptsIn.1 hy) (mem_ptsIn.1 hy') (mem_ptsIn.1 hj)).regAt, norm_mul, hg, mul_one]
    have hnu : ∀ l, P.nu e 0 σ y (x l) ^ 2 =
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2 *
          Real.exp (-((e : ℝ) * (P.L.φ σ).φ (i PUnit.unit) y)) := fun l => by
      rw [nu_eq k X p P e 0 (x l) (hx.mem l) σ y _ _ hy' hj, mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    set S := ∑ l, ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2 with hS
    have hSpos : 0 < S := by
      obtain ⟨l, hl⟩ := hx.cover (under y)
      have h0 := norm_pos_iff.2 (ratVal_ne_zero (hl _ _ (mem_ptsIn.1 hy') (mem_ptsIn.1 hj)))
      exact (pow_pos h0 2).trans_le (Finset.single_le_sum (f := fun l =>
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ l))
    have hsum : ∑ l, P.nu e 0 σ y (x l) ^ (2 * 1) = Real.exp (-((e : ℝ) * (P.L.φ σ).φ (i PUnit.unit) y)) * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_one, hnu l, mul_comm]
    have hu1 := hu' σ y
    rw [hsum, Real.log_mul (Real.exp_pos _).ne' hSpos.ne', Real.log_exp] at hu1
    change (((P.L.φ σ).addFn (u.u σ)).zpow (e : ℤ)).φ i y = _
    refine (Weight.zpow_φ _ _ _ _).trans ?_
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    change ((e : ℤ) : ℝ) * ((P.L.φ σ).φ (i PUnit.unit) y + u.u σ y) =
      Real.log (∑ l, ‖valR y.1 ((P.L.pow e).B.U i) ((s l).f i)‖ ^ 2)
    simp only [hA, ← hS]
    rw [hu1]
    push_cast
    field_simp
    ring

end GlobalTheory.HSAmp.GenMap
end
end

section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

variable {K : Type} [Field K] {D : ℕ}

theorem ratR_zero_eq_closure (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0) :
    ratR x 0 = Subring.closure (Set.range fun j : Fin D => x j.succ / x 0) := by
  refine le_antisymm (Subring.closure_le.2 ?_) (Subring.closure_mono ?_)
  · rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [div_self h0]; exact Subring.one_mem _
    · exact Subring.subset_closure ⟨i, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩

theorem ratR_zero_le_ratF (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0) : ratR x 0 ≤ (ratF x).toSubring := by
  rw [ratR_zero_eq_closure x h0]
  exact Subring.closure_le.2 fun _ h => Subfield.subset_closure h

theorem exists_ringEquiv_ratR (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0)
    (hind : AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0)) :
    ∃ e : MvPolynomial (Fin D) ℤ ≃+* ratR x 0, ∀ j, (e (X j) : K) = x j.succ / x 0 := by
  have hS : (Algebra.adjoin ℤ (Set.range fun j : Fin D => x j.succ / x 0)).toSubring = ratR x 0 := by
    rw [Algebra.adjoin_int, ratR_zero_eq_closure x h0]; rfl
  refine ⟨hind.aevalEquiv.toRingEquiv.trans (RingEquiv.subringCongr hS), fun j => ?_⟩
  have := hind.algebraMap_aevalEquiv (X j)
  rw [aeval_X] at this
  exact this

end GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp



theorem norm_aeval_trace_le : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (B : Subring K) (hB : ∀ l, x l / x 0 ∈ B), (∀ b ∈ B, IsIntegral (ratR x 0) b) →
    ∀ (w : B) (T : MvPolynomial (Fin (D + 1)) ℤ),
    (Algebra.trace (ratF x) K (w : K) : K) = aeval (fun l => x l / x 0) T →
    ∀ (z : Fin (D + 1) → ℂ) (M : ℝ), z 0 = 1 →
    (∀ φ : B →+* ℂ, (∀ l, φ ⟨x l / x 0, hB l⟩ = z l) → ‖φ w‖ ≤ M) →
    ‖aeval z T‖ ≤ Module.finrank (ratF x) K * M := by
  intro K _ _ D x hx hind hfin B hB hint w T htr z M hz0 hM
  have h0 := hx 0
  have hAF := ratR_zero_le_ratF x h0
  have memA : ∀ l, x l / x 0 ∈ ratR x 0 := fun l => Subring.subset_closure ⟨l, rfl⟩
  have hAB : ratR x 0 ≤ B := Subring.closure_le.2 (by rintro _ ⟨l, rfl⟩; exact hB l)
  letI : Algebra (ratR x 0) (ratF x) := (Subring.inclusion hAF).toAlgebra
  letI : Algebra (ratR x 0) B := (Subring.inclusion hAB).toAlgebra
  haveI : IsScalarTower (ratR x 0) (ratF x) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (ratR x 0) B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨e, he⟩ := exists_ringEquiv_ratR x h0 hind
  haveI : UniqueFactorizationMonoid (ratR x 0) := e.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have hinjF : Function.Injective (algebraMap (ratR x 0) (ratF x)) := Subring.inclusion_injective hAF
  have hinjB : Function.Injective (algebraMap (ratR x 0) B) := Subring.inclusion_injective hAB
  haveI : FaithfulSMul (ratR x 0) (ratF x) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinjF
  haveI : IsFractionRing (ratR x 0) (ratF x) := by
    refine IsFractionRing.of_field _ _ fun y => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 y.2
    rw [← ratR_zero_eq_closure x h0] at ha hb
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext (by rw [Subfield.coe_div]; exact hab.symm)⟩
  have hwint : IsIntegral (ratR x 0) (w : K) := hint w w.2
  have hmin : minpoly (ratF x) (w : K) = (minpoly (ratR x 0) (w : K)).map (algebraMap (ratR x 0) (ratF x)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (ratF x) hwint
  have hminB : minpoly (ratR x 0) w = minpoly (ratR x 0) (w : K) :=
    (minpoly.algHom_eq (IsScalarTower.toAlgHom (ratR x 0) B K) Subtype.val_injective w).symm
  haveI : Algebra.IsIntegral (ratR x 0) B :=
    ⟨fun b => (isIntegral_algHom_iff (IsScalarTower.toAlgHom (ratR x 0) B K) Subtype.val_injective).1 (hint b b.2)⟩
  set p := minpoly (ratR x 0) (w : K) with hp
  have hpm : p.Monic := minpoly.monic hwint

  obtain ⟨m, htr', hmdeg⟩ : ∃ m : ℕ, Algebra.trace (ratF x) K (w : K) = m * -(minpoly (ratF x) (w : K)).nextCoeff ∧
      m * (minpoly (ratF x) (w : K)).natDegree = Module.finrank (ratF x) K :=
    ⟨_, trace_eq_finrank_mul_minpoly_nextCoeff (ratF x) (w : K), by
      rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite (ratF x) (w : K)), mul_comm,
        Module.finrank_mul_finrank]⟩
  rw [hmin, hpm.natDegree_map] at hmdeg
  set c : ratR x 0 := m * -p.nextCoeff with hc
  have hcF : Algebra.trace (ratF x) K (w : K) = algebraMap (ratR x 0) (ratF x) c := by
    rw [htr', hmin, Polynomial.nextCoeff_map hinjF, hc, map_mul, map_neg, map_natCast]
  rw [hcF] at htr

  let a : Fin (D + 1) → ratR x 0 := fun l => ⟨x l / x 0, memA l⟩
  have hcT : c = aeval a T := by
    apply Subtype.val_injective
    refine htr.trans ?_
    have := AlgHom.congr_fun (MvPolynomial.comp_aeval a (ratR x 0).subtype.toIntAlgHom) T
    simp only [AlgHom.comp_apply] at this
    exact this.symm

  let ψ : ratR x 0 →+* ℂ := (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) fun j : Fin D => z j.succ).comp e.symm.toRingHom
  have hψ : ∀ l, ψ (a l) = z l := by
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · have : a 0 = 1 := Subtype.ext (div_self h0)
      rw [this, map_one, hz0]
    · have : a j.succ = e (X j) := Subtype.ext (he j).symm
      rw [this]
      show MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : Fin D => z j.succ) (e.symm (e (X j))) = _
      rw [RingEquiv.symm_apply_apply, eval₂Hom_X']
  have hψc : ψ c = aeval z T := by
    rw [hcT]
    have := AlgHom.congr_fun (MvPolynomial.comp_aeval a ψ.toIntAlgHom) T
    simp only [AlgHom.comp_apply] at this
    refine this.trans ?_
    rw [show (fun i => ψ.toIntAlgHom (a i)) = z from funext fun l => hψ l]

  set q := p.map ψ with hq
  have hqm : q.Monic := hpm.map ψ
  have hsum : q.nextCoeff = -q.roots.sum :=
    (IsAlgClosed.splits q).nextCoeff_eq_neg_sum_roots_of_monic hqm
  have hqn : q.nextCoeff = ψ p.nextCoeff :=
    Polynomial.nextCoeff_map_of_leadingCoeff_ne_zero ψ (by rw [hpm.leadingCoeff, map_one]; exact one_ne_zero)
  have hcard : q.roots.card = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hpm.natDegree_map]
  have hroots : ∀ r ∈ q.roots, ‖r‖ ≤ M := by
    intro r hr
    have hr' : ((minpoly (ratR x 0) w).map ψ).IsRoot r := by
      rw [hminB]; exact (Polynomial.mem_roots hqm.ne_zero).1 hr
    obtain ⟨φ, hφ, hφw⟩ := (GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom (ratR x 0) B hinjB w ψ r).1 hr'
    rw [← hφw]
    refine hM φ fun l => ?_
    rw [← hψ l, ← hφ]
    rfl
  have hval : aeval z T = (m : ℂ) * q.roots.sum := by
    rw [← hψc, hc, map_mul, map_neg, map_natCast, ← hqn, hsum, neg_neg]
  rw [hval, norm_mul, Complex.norm_natCast, ← hmdeg, Nat.cast_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (norm_multiset_sum_le _).trans ?_
  refine (Multiset.sum_le_card_nsmul _ M fun y hy => ?_).trans ?_
  · obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hy
    exact hroots r hr
  · rw [Multiset.card_map, hcard, nsmul_eq_mul]

end GlobalTheory.HSAmp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ENNReal

namespace GlobalTheory.HSAmp

theorem exists_isRatio_chernInt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ (L : HermLB p), L.SemiPos D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D),
    ∃ ρ : CxPts p σ → ℝ, ω.IsRatio (L.φ σ) ρ ∧ (∀ y, 0 ≤ ρ y) ∧ ∀ f : CxPts p σ → ℝ, Continuous f →
      (L.φ σ).chernInt D Set.univ f = ∫ y, f y * ρ y ∂ω.meas := by
  intro k _ X _ p D hX hG L hL σ ω
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hG σ
  have hcov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source := fun y =>
    have ⟨i, hi⟩ := R.cover y
    ⟨R.chart i, hi⟩
  choose c₀ hc₀ using hcov
  let ρ : CxPts p σ → ℝ := fun y => (c₀ y).chernDens (L.φ σ) y / ω.dens (c₀ y) y
  have key : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, c.chernDens (L.φ σ) y = ρ y * ω.dens c y := by
    intro c y hy
    have hpos := ω.pos (c₀ y) y (hc₀ y)
    rw [c.chernDens_trans (c₀ y) (L.cInf σ) hy (hc₀ y), ω.trans c (c₀ y) y hy (hc₀ y)]
    simp only [ρ]
    field_simp
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y =>
    div_nonneg ((c₀ y).chernDens_nonneg (L.cInf σ) (hL σ) (hc₀ y)) (ω.pos _ _ (hc₀ y)).le

  have hρc : Continuous ρ := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    set c := c₀ y
    set i := pick (L.φ σ).isLB y
    have hyi : y ∈ ptsIn p σ (L.B.U i) := mem_pick _ y
    set O : Set (CxPts p σ) := c.e.source ∩ ptsIn p σ (L.B.U i) with hO
    have hOo : IsOpen O := c.e.open_source.inter (isOpen_ptsIn _)
    have hyO : y ∈ O := ⟨hc₀ y, hyi⟩
    set U' : Set (V D) := c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (L.B.U i)
    have hU' : IsOpen U' := isOpen_over c.e (isOpen_ptsIn _)
    have h2 : ContDiffOn ℝ 2 (fun v => (L.φ σ).φ i (c.e.symm v)) U' :=
      (contDiffOn_chart ((L.cInf σ) i) c).of_le (by norm_cast)
    have hmap : Set.MapsTo c.e O U' := fun z hz => mem_over c.e hz.1 hz.2
    have hent : ∀ a b, ContinuousOn (fun z => c.hess (L.φ σ) i z a b) O := fun a b =>
      (continuousOn_cHess_of_contDiffOn_two D U' _ hU' h2 a b).comp (c.e.continuousOn.mono fun z hz => hz.1) hmap
    have hdet : ContinuousOn (fun z => c.chernDens (L.φ σ) z) O := by
      have hm : ContinuousOn (fun z => c.hess (L.φ σ) i z) O :=
        continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => hent a b
      have hc : Continuous fun M : Matrix (Fin D) (Fin D) ℂ => (D.factorial / Real.pi ^ D : ℝ) * M.det.re :=
        continuous_const.mul (Complex.continuous_re.comp continuous_id.matrix_det)
      refine (hc.comp_continuousOn hm).congr fun z hz => ?_
      exact c.chernDens_eq (L.cInf σ) hz.1 hz.2
    have hq : ContinuousOn (fun z => c.chernDens (L.φ σ) z / ω.dens c z) O :=
      hdet.div ((ω.cont c).mono fun z hz => hz.1) fun z hz => (ω.pos c z hz.1).ne'
    refine (hq.congr fun z hz => ?_).continuousAt (hOo.mem_nhds hyO)
    rw [key c z hz.1, mul_div_cancel_right₀ _ (ω.pos c z hz.1).ne']
  have hm : Measurable fun y => ENNReal.ofReal (ρ y) := hρc.measurable.ennreal_ofReal
  have hneg : (L.φ σ).chernPart D (-1) = 0 := Weight.chernPart_neg_eq_zero (L.cInf σ) (hL σ)
  have hmeas : (L.φ σ).chernPart D 1 = ω.meas.withDensity fun y => ENNReal.ofReal (ρ y) := by
    refine ext_of_cover (fun c : AlgChart p σ D => c.e.source) (fun c => c.e.open_source)
      (fun y => ⟨c₀ y, hc₀ y⟩) fun c A hA hAc => ?_
    have hr : ω.meas.restrict A = (chartMeas c.e fun y => ENNReal.ofReal (ω.dens c y)).restrict A := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.restrict_apply hT, VolDens.meas,
        glueMeas_apply _ _ (fun a a' => a.holo_trans a') (fun a a' z hz hz' => by
          rw [ω.trans a a' z hz hz', ENNReal.ofReal_mul (sq_nonneg _)]) c (hT.inter hA)
          (Set.inter_subset_right.trans hAc)]
    have hsy : AEMeasurable c.e.symm (volume.restrict c.e.target) :=
      c.e.continuousOn_symm.aemeasurable c.e.open_target.measurableSet
    have hdm : AEMeasurable ((fun y => ENNReal.ofReal (ω.dens c y)) ∘ c.e.symm) (volume.restrict c.e.target) :=
      (ENNReal.continuous_ofReal.comp_continuousOn ((ω.cont c).comp c.e.continuousOn_symm
        fun v hv => c.e.map_target hv)).aemeasurable c.e.open_target.measurableSet
    have hI := measurableSet_image c.e hA hAc
    have hIt : c.e '' A ⊆ c.e.target := by rintro _ ⟨z, hz, rfl⟩; exact c.e.map_source (hAc hz)
    rw [Weight.chernPart_apply (L.cInf σ) 1 c hA hAc, withDensity_apply _ hA, hr, ← lintegral_indicator hA, chartMeas,
      lintegral_map' (hm.indicator hA).aemeasurable (hsy.mono_ac (withDensity_absolutelyContinuous _ _)),
      lintegral_withDensity_eq_lintegral_mul₀ hdm (g := fun v => A.indicator (fun y => ENNReal.ofReal (ρ y)) (c.e.symm v))
        ((hm.indicator hA).comp_aemeasurable hsy),
      ← Set.inter_eq_left.2 hIt, ← Measure.restrict_restrict hI, ← lintegral_indicator hI]
    refine setLIntegral_congr_fun c.e.open_target.measurableSet fun v hv => ?_
    by_cases hvA : c.e.symm v ∈ A
    · have hvI : v ∈ c.e '' A := ⟨_, hvA, c.e.right_inv hv⟩
      simp only [Set.indicator_of_mem hvI, Pi.mul_apply, Set.indicator_of_mem hvA, Function.comp_apply,
        Units.val_one, Int.cast_one, one_mul]
      rw [key c _ (hAc hvA), ENNReal.ofReal_mul (hρ0 _), mul_comm]
    · have hvI : v ∉ c.e '' A := by
        rintro ⟨z, hz, rfl⟩
        exact hvA (by rwa [c.e.left_inv (hAc hz)])
      simp only [Set.indicator_of_notMem hvI, Pi.mul_apply, Set.indicator_of_notMem hvA, mul_zero]
  refine ⟨ρ, ⟨hρc, key⟩, hρ0, fun f _ => ?_⟩
  have hn : Measurable fun y => (ρ y).toNNReal := hρc.measurable.real_toNNReal
  rw [Weight.chernInt, hneg, Measure.restrict_univ, Measure.restrict_univ, integral_zero_measure, sub_zero, hmeas]
  change ∫ y, f y ∂ω.meas.withDensity (fun y => ((ρ y).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hn]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hρ0 y), smul_eq_mul]
  exact mul_comm _ _

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem exists_tens_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (S : Set Y), S.Finite →
      ∃ (A : HermLB q) (s : (M.tens A).B.Sec) (u : A.B.Sec), S ⊆ nonzeroLocus s ∧ S ⊆ nonzeroLocus u := by
  intro k _ Y q hq M S hS
  have := hq.isNoetherian
  obtain ⟨N, j, hj, e⟩ := hq.isProjOver
  let A₀ : HermLB q := (ProjSpace.hermitianTwistingSheaf k N).pull j e
  have hA : IsAmpleLB A₀.B := by
    dsimp [A₀, HermLB.pull, ProjSpace.hermitianTwistingSheaf, HermLB.fs]
    exact (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  obtain ⟨n, h₁, h₂⟩ := (tendsto_natCast_atTop_atTop.eventually
    ((hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS).and
      (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv Y) hS))).exists
  obtain ⟨s, hs⟩ := h₁ (CechPic.tens M.B (lbPow A₀.B n)) (isLB_tens M.isLB (isLB_lbPow A₀.isLB n)) (by
    rw [cls_tens M.isLB (isLB_lbPow A₀.isLB n), cls_lbPow A₀.isLB, natCast_zsmul])
  obtain ⟨u, hu⟩ := h₂ (lbPow A₀.B n) (isLB_lbPow A₀.isLB n) (by
    rw [cls_lbPow A₀.isLB, cls_triv, zero_add, natCast_zsmul])
  exact ⟨A₀.pow n, s, u, hs, hu⟩

end GlobalTheory.MixHt
end
end
