module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Graded
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Partners
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Cast.SetInterval
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section GrdComm

variable {LL Ks D : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]

theorem Pf_LvGam_grd_comm (σ τ : Ks ≃ₐ[LL] Ks) (a b : LLˣ) (h : ∀ x, σ (τ x) = τ (σ x))
    (f : Amb LL Ks D) : grd τ b (grd σ a f) = grd σ a (grd τ b f) := by
  apply HahnModule.ext
  funext i
  change cf (grd τ b (grd σ a f)) i = cf (grd σ a (grd τ b f)) i
  rw [SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, map_smul, map_smul, smul_smul, smul_smul,
    SlopeTestRemainingChoices.tD_comm σ τ h, mul_comm]

end GrdComm

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem Pf_LvGam_στ (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (s : ℕ) (j : DeltaT PD.p) (x : KsW W s) :
    (levW W uZ ιZ s).σ ((levW W uZ ιZ s).τ j x) = (levW W uZ ιZ s).τ j ((levW W uZ ιZ s).σ x) := by
  funext ζ
  show x (powR LL PD.p s (redU PD.p s j.1) (powR LL PD.p s (redU PD.p s uZ) ζ)) =
    x (powR LL PD.p s (redU PD.p s uZ) (powR LL PD.p s (redU PD.p s j.1) ζ))
  rw [powR_powR, powR_powR, mul_comm]

theorem gamInv_holds (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (T : LocLat G Qp LL O) (c : ZMod n) :
    ∀ (s : ℕ) (f : Amb LL (KsW W s) (Dc W T c)), (levW W uZ ιZ s).Inv f →
      (levW W uZ ιZ s).Inv ((levW W uZ ιZ s).γ f) := by
  intro s f hf j
  show grd ((levW W uZ ιZ s).τ j) ((levW W uZ ιZ s).a j) (grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u f) =
    grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u f
  rw [Pf_LvGam_grd_comm _ _ _ _ (Pf_LvGam_στ uZ ιZ s j)]
  exact congrArg (grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u) (hf j)

theorem Pf_LvGam_coeff_neg {Ks : Type} [CommRing Ks] (x : PowerSeries Ks) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ Ks x).coeff (Int.negSucc k) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  simp

theorem gamRho_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (c : ZMod n)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hK : W.gamK = W.gam)
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL))) :
    ∀ (s : ℕ) (a : PowerSeries O),
      grdB (levW W uZ ιZ s).σ (levW W uZ ιZ s).u (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)) =
        HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s ((baseIdOf hR).Bs.γ a)) := by
  intro s a
  refine HahnSeries.ext (funext fun i => ?_)
  change algebraMap LL (KsW W s) (((levW W uZ ιZ s).u ^ i : LLˣ) : LL) *
    (levW W uZ ιZ s).σ ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i) = _
  rcases i with k | k
  · rw [Int.ofNat_eq_natCast, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff]
    funext ζ
    have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
      (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
    have hv : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gamK : O) -
        (((redU PD.p s uZ : (ZMod (PD.p ^ (s + 1)))ˣ) : ZMod (PD.p ^ (s + 1))).val : LL)) := by
      rw [hK]
      exact huZ (s + 1)
    have hL := lev_Γ W.gamK c ζ ((powR LL PD.p s (redU PD.p s uZ) ζ : Rs LL PD.p s) : LL) (s + 1) _
      hprim hv rfl (fun _ => (baseIdOf hR).ι a)
    have hR1 : PowerSeries.coeff k (rhoL hR c s ((baseIdOf hR).Bs.γ a)) ζ =
        PowerSeries.coeff k (W.lev c ζ (W.γA W.gamK (fun _ => (baseIdOf hR).ι a))) := by
      rw [rhoL, RingHom.comp_apply, coeff_psPi]
      show PowerSeries.coeff k (W.lev c ζ (fun _ => (baseIdOf hR).ι ((baseIdOf hR).Bs.γ a))) = _
      rw [(baseIdOf hR).ι_γ a]
      rfl
    have hL1 : PowerSeries.coeff k (rhoL hR c s a) (powR LL PD.p s (redU PD.p s uZ) ζ) =
        PowerSeries.coeff k (W.lev c ((powR LL PD.p s (redU PD.p s uZ) ζ : Rs LL PD.p s) : LL)
          (fun _ => (baseIdOf hR).ι a)) := by
      rw [rhoL, RingHom.comp_apply, coeff_psPi]
      rfl
    rw [hR1, hL, PowerSeries.coeff_rescale, ← hL1, hK]
    show (((levW W uZ ιZ s).u ^ (k : ℤ) : LLˣ) : LL) *
      PowerSeries.coeff k (rhoL hR c s a) (powR LL PD.p s (redU PD.p s uZ) ζ) = _
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  · rw [Pf_LvGam_coeff_neg, Pf_LvGam_coeff_neg, map_zero, mul_zero]

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}

theorem rho_ff_eq_unit_mul [IsDomain O] (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) {j M g η : ℕ} {kind : ℕ → Kind} {b : ℕ → ℕ}
    (hk1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (hU : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) (hj : j ≤ ell)
    (s : ℕ) (hs : s < ell) :
    ∃ ε : (PowerSeries (KsW W s))ˣ, rhoL hR c s ((baseIdOf hR).Bs.ff' ell j M g) =
      (ε : PowerSeries (KsW W s)) * PowerSeries.X ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s := by
  obtain ⟨u, hu⟩ := filtration_shape_holds O (baseIdOf hR).Bs ell j M g hj (frobenius_uniformizer_identity hR)
  obtain ⟨ε, hε⟩ := hk1b s hs
  have hε' : rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X := hε
  have hX : IsUnit (rhoL hR c s PowerSeries.X) := (hU s hs).1
  have hp : ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')) := (hU s hs).2
  have hV : IsUnit (rhoL hR c s (u : PowerSeries O) * rhoL hR c s PowerSeries.X ^ M *
      ∏ s' ∈ (Finset.range ell).erase s,
        rhoL hR c s ((baseIdOf hR).Bs.p s' ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s')) := by
    refine ((u.isUnit.map (rhoL hR c s)).mul (hX.pow M)).mul
      (Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun s' hs' => ?_)
    rw [map_pow]
    exact (hp s' (Finset.mem_range.1 (Finset.mem_of_mem_erase hs')) (Finset.ne_of_mem_erase hs')).pow _
  refine ⟨hV.unit * ε ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s, ?_⟩
  rw [hu, map_mul, map_mul, map_pow, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), map_pow,
    hε', Units.val_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val]
  ring

theorem rho_sub_mem [IsDomain O] (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) {j M g η : ℕ} {kind : ℕ → Kind} {b : ℕ → ℕ}
    (hk1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (hU : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) (hj : j ≤ ell)
    (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M) (s : ℕ) (hs : s < ell) :
    ∀ z ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)),
      ∃ y ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0),
        z = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s ((baseIdOf hR).Bs.ff' ell j M g)) • y := by
  intro z hz
  obtain ⟨ε, hε⟩ := rho_ff_eq_unit_mul Hy hk1b hU hj s hs
  have hle : ordF ell j (baseIdOf hR).Bs.ℓ M g s ≤ ((baseIdOf hR).Bs.ℓ - 1) * M := by
    unfold ordF
    split_ifs <;> omega
  have hTw : (fun i : ℤ => Tw (LL := LL) (D := Dc W T c) 0 (i + -((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ))) =
      Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) := by
    funext i
    unfold Tw
    by_cases h : ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) ≤ i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have hz' : tp (KsW W s) (-((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)) • z ∈
      Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0) :=
    (xi_shift_holds LL (KsW W s) (Dc W T c) _ _ z).2 (by rw [hTw]; exact hz)
  refine ⟨HahnSeries.ofPowerSeries ℤ (KsW W s) ((↑ε⁻¹ : PowerSeries (KsW W s)) *
      PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M - ordF ell j (baseIdOf hR).Bs.ℓ M g s)) •
      (tp (KsW W s) (-((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)) • z),
    xi_module_structure LL (KsW W s) (Dc W T c) _ (tw_mono 0) _ _ hz', ?_⟩
  have hmul : (ε : PowerSeries (KsW W s)) * PowerSeries.X ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s *
      ((↑ε⁻¹ : PowerSeries (KsW W s)) *
        PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M - ordF ell j (baseIdOf hR).Bs.ℓ M g s)) =
      PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M) := by
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add, Nat.add_sub_cancel' hle]
  rw [hε, ← mul_smul, ← map_mul, hmul, ← mul_smul, HahnSeries.ofPowerSeries_X_pow, tp,
    HahnSeries.single_mul_single, add_neg_cancel, one_mul, HahnSeries.single_zero_one, one_smul]

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Conv

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem Pf_LvExp_coeff_neg (x : PowerSeries R) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff (Int.negSucc k) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  simp

theorem Pf_LvExp_coeff_smul (x : PowerSeries R) (y : HahnModule ℤ R M) (m : ℤ)
    (hy : ∀ k < m, ((HahnModule.of R).symm y).coeff k = 0) (k : ℤ) (N : ℕ) (hN : k - m < N) :
    ((HahnModule.of R).symm (HahnSeries.ofPowerSeries ℤ R x • y)).coeff k =
      ∑ j ∈ Finset.range N, PowerSeries.coeff j x • ((HahnModule.of R).symm y).coeff (k - j) := by
  rw [HahnModule.coeff_smul]
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ => ((j : ℤ), k - j)) ?_ ?_ ?_ ?_
  · intro j _ hj
    have h1 : PowerSeries.coeff j x ≠ 0 := fun h => hj (by rw [h, zero_smul])
    have h2 : ((HahnModule.of R).symm y).coeff (k - j) ≠ 0 := fun h => hj (by rw [h, smul_zero])
    rw [Finset.mem_vaddAntidiagonal]
    refine ⟨?_, ?_, ?_⟩
    · rw [HahnSeries.mem_support, HahnSeries.ofPowerSeries_apply_coeff]
      exact h1
    · rw [HahnSeries.mem_support]
      exact h2
    · show (j : ℤ) + (k - j) = k
      ring
  · intro j _ _ j' _ _ h
    exact_mod_cast (Prod.mk.inj h).1
  · intro ij hij hne
    rw [Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    obtain ⟨i, i'⟩ := ij
    simp only at h1 h2 h3 hne
    cases i with
    | negSucc t => exact absurd (Pf_LvExp_coeff_neg x t) ((HahnSeries.mem_support _ _).1 h1)
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast, vadd_eq_add] at h3 hne
      have hi' : i' = k - j := by omega
      have hm' : m ≤ i' := by
        by_contra hlt
        push Not at hlt
        exact (HahnSeries.mem_support _ _).1 h2 (hy _ hlt)
      refine ⟨j, Finset.mem_range.2 (by omega), ?_, ?_⟩
      · rw [← hi']
        rwa [HahnSeries.ofPowerSeries_apply_coeff] at hne
      · simp [hi']
  · intro j _ _
    dsimp only
    rw [HahnSeries.ofPowerSeries_apply_coeff]

theorem Pf_LvExp_finsum (f : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • g (k - j) = ∑ j ∈ Finset.range N, PowerSeries.coeff j f • g (k - j) := by
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply hj
  show PowerSeries.coeff j f • g (k - j) = 0
  rw [hg (k - j) (by omega), smul_zero]

end Conv

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem Pf_LvExp_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab


open Classical in
def Pf_LvExp_Φ (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

theorem Pf_LvExp_Φ_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (f : Rs LL PD.p s → D) : Pf_LvExp_Φ W s D (toKsD W s D f) = f := by
  simp only [Pf_LvExp_Φ, toKsD, LinearEquiv.trans_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem Pf_LvExp_Φ_smul (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (f : KsW W s)
    (z : KsW W s ⊗[LL] D) (ζ : Rs LL PD.p s) :
    Pf_LvExp_Φ W s D (f • z) ζ = f ζ • Pf_LvExp_Φ W s D z ζ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul g d => simp [Pf_LvExp_Φ, TensorProduct.smul_tmul', TensorProduct.piScalarRightHom_tmul, mul_smul]
  | add z z' hz hz' => rw [smul_add, map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, hz, hz', smul_add]

theorem Pf_LvExp_coeff_expN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) : ((HahnModule.of (KsW W s)).symm (expN Lb s T c y)).coeff k = coefN Lb s T c y k :=
  rfl

theorem Pf_LvExp_Φ_coefN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) (ζ : Rs LL PD.p s) :
    ((Pf_LvExp_Φ W s (Dc W T c) (coefN Lb s T c y k) ζ : Dc W T c) : T.V ⊗[Qp] B) =
      Lb.levB T c ζ y k := by
  simp only [coefN, Pf_LvExp_Φ_toKsD]

theorem expSemi_holds (Lb : LevB W) (hR : Ring9 W) (T : LocLat G Qp LL O) (c : ZMod n)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k)) :
    ExpSemi Lb hR T c := by
  intro s a y hy
  obtain ⟨m, hm⟩ := bdd_coefN Lb s T c y
  have hm' : ∀ k < m, coefN Lb s T c y k = 0 := fun k hk => by
    by_contra h
    exact absurd (hm h) (not_le.2 hk)
  apply (HahnModule.of (KsW W s)).symm.injective
  ext k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N := ⟨(k - m).toNat + 1, by omega⟩
  rw [Pf_LvExp_coeff_smul _ _ m (fun k' hk' => by rw [Pf_LvExp_coeff_expN]; exact hm' k' hk') k N hN]
  simp only [Pf_LvExp_coeff_expN]
  apply (Pf_LvExp_Φ W s (Dc W T c)).injective
  funext ζ

  rw [map_sum, Finset.sum_apply]
  simp only [Pf_LvExp_Φ_smul]
  apply Subtype.ext
  apply Pf_LvExp_ιV_inj (PD := PD) T

  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Pf_LvExp_Φ_coefN]
  simp only [← levN_eq]
  have hg : ∀ k' < m, W.levN T c ζ y k' = 0 := fun k' hk' => by
    rw [levN_eq, ← Pf_LvExp_Φ_coefN Lb s T c y k' ζ, hm' k' hk', map_zero]
    simp
  rw [show (⟨_, hy⟩ : ↥(W.N T)) = (baseIdOf hR).d a • y from rfl, W.levN_smul,
    Pf_LvExp_finsum _ _ m hg k N hN]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := congrArg (PowerSeries.coeff j) (map_eval_rhoL hR c s a ζ)
  rw [PowerSeries.coeff_map] at h
  exact h.symm

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_HuZ_v_dvd (W : LocWach PD LL O v n) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (k : ℕ) (z : ℤ_[PD.p]) (hz : (PD.p : ℤ_[PD.p]) ^ k ∣ z) :
    (k : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)) := by
  obtain ⟨y, rfl⟩ := hz
  rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast, AddValuation.map_mul,
    AddValuation.map_pow, W.v_l, nsmul_one]
  exact le_add_of_nonneg_right (hv_int _)

theorem hv_holds (W : LocWach PD LL O v n) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)) :=
  fun s z hz => Pf_HuZ_v_dvd W hv_int (s + 1) z hz

theorem huZ_holds (hu : ιZ uZ = (W.χΓ W.gam : O)) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)) := by
  intro k
  have : NeZero (PD.p ^ k) := ⟨pow_ne_zero _ (Fact.out : PD.p.Prime).ne_zero⟩
  have hdvd : (PD.p : ℤ_[PD.p]) ^ k ∣
      (uZ : ℤ_[PD.p]) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : ℤ_[PD.p]) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_self]
  have h := Pf_HuZ_v_dvd (ιZ := ιZ) W hv_int k _ hdvd
  rwa [map_sub, map_natCast, hu, map_sub, map_natCast] at h

end Formalism.MainNotions.N.Ln03.Pf
end
end
