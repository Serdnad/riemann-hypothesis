module

import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvEquiv
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Graded
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Graded

variable {LL Ks : Type} [Field LL] [CommRing Ks] [Algebra LL Ks]

theorem grdB_zero' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a 0 = 0 := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((0 : HahnSeries ℤ Ks).coeff n) = (0 : HahnSeries ℤ Ks).coeff n
  simp

theorem grdB_one' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a 1 = 1 := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((1 : HahnSeries ℤ Ks).coeff n) = (1 : HahnSeries ℤ Ks).coeff n
  by_cases h : n = 0
  · subst h
    simp
  · simp [HahnSeries.coeff_one, h]

theorem grdB_mul' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x y : HahnSeries ℤ Ks) :
    grdB τ a (x * y) = grdB τ a x * grdB τ a y := by
  apply Formalism.MainNotions.N.Ln03.Pf.Pf_LvEquiv_grdB_mul <;> assumption

theorem grdB_ringInverse (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) {X : HahnSeries ℤ Ks} (hX : grdB τ a X = X) :
    grdB τ a (Ring.inverse X) = Ring.inverse X := by
  by_cases hu : IsUnit X
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    have h1 : grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * ↑u = 1 := by
      conv_lhs => rw [← hX]
      rw [← grdB_mul', Units.inv_mul, grdB_one']
    calc grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks)
        = grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = (grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * ↑u) * ↑u⁻¹ := by ring
      _ = ↑u⁻¹ := by rw [h1, one_mul]
  · rw [Ring.inverse_non_unit _ hu, grdB_zero']

theorem ofPS_coeff_neg {R : Type} [CommRing R] (x : PowerSeries R) {i : ℤ} (hi : i < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff i = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_of_notMem_range (by
    rintro ⟨m, hm⟩
    simp at hm
    omega)

end Graded

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem val_sub_toZModPow (W : LocWach PD LL O v n) (valRing : ValRing O v) (ιZ : ℤ_[PD.p] →+* O)
    (ω : ℤ_[PD.p]) (N : ℕ) :
    ((N : ℕ) : WithTop ℚ) ≤
      v (algebraMap O LL (ιZ ω) - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : LL)) := by
  have : NeZero (PD.p ^ N) := ⟨pow_ne_zero _ PD.hp.ne_zero⟩
  have hk : ω - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : ℤ_[PD.p]) ∈
      RingHom.ker (PadicInt.toZModPow (p := PD.p) N) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨y, hy⟩ := hk
  have e : algebraMap O LL (ιZ ω) - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : LL) =
      ((PD.p : ℕ) : LL) ^ N * algebraMap O LL (ιZ y) := by
    rw [← map_natCast (algebraMap O LL), ← map_natCast ιZ, ← map_sub, ← map_sub, hy, map_mul, map_mul,
      map_pow, map_pow, map_natCast, map_natCast]
  rw [e, AddValuation.map_mul, AddValuation.map_pow, W.v_l, nsmul_one]
  exact le_add_of_nonneg_right (valRing.2.2 _)

variable {W : LocWach PD LL O v n}

theorem delta_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (c : ZMod n)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF, algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ω.1))
    (valRing : ValRing O v) :
    DeltaRho hR uZ ιZ c := by
  intro s j a
  obtain ⟨g, hg, hχ⟩ := hω j
  apply HahnSeries.ext
  funext i
  by_cases hi : i < 0
  · show algebraMap LL (KsW W s) ((((levW W uZ ιZ s).a j) ^ i : LLˣ) : LL) *
        ((levW W uZ ιZ s).τ j) ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i) =
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i
    rw [ofPS_coeff_neg _ hi, map_zero, mul_zero]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hi)
    show algebraMap LL (KsW W s) ((((levW W uZ ιZ s).a j) ^ (k : ℤ) : LLˣ) : LL) *
        ((levW W uZ ιZ s).τ j) ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff (k : ℤ)) =
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff (k : ℤ)
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    have hc : ∀ ζ' : Rs LL PD.p s, (PowerSeries.coeff k (rhoL hR c s a)) ζ' =
        PowerSeries.coeff k (W.lev c (ζ' : LL) ((baseIdOf hR).d a)) := fun ζ' => by
      show Pi.evalRingHom (fun _ => LL) ζ' (PowerSeries.coeff k (rhoL hR c s a)) = _
      rw [← PowerSeries.coeff_map, map_eval_rhoL]
      rfl
    funext ζ
    change ((((levW W uZ ιZ s).a j) ^ (k : ℤ) : LLˣ) : LL) *
      (PowerSeries.coeff k (rhoL hR c s a)) (powR LL PD.p s (redU PD.p s j.1) ζ) =
      (PowerSeries.coeff k (rhoL hR c s a)) ζ
    rw [hc, hc]
    have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) := (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
    have hv := val_sub_toZModPow W valRing ιZ (j.1 : ℤ_[PD.p]) (s + 1)
    rw [← hχ] at hv
    have hL := lev_Γ g c ζ _ (s + 1) _ hprim hv rfl ((baseIdOf hR).d a)
    rw [BaseId.γA_Δ _ g hg] at hL
    rw [hL, PowerSeries.coeff_rescale, hχ]
    congr 1

theorem loclInv_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (T : LocLat G Qp LL O)
    (c : ZMod n) {r : ℕ} (Λ : PowerSeries O) (lam : Fin r → Dc W T c) (hΔ : DeltaRho hR uZ ιZ c) :
    LocLInv hR uZ ιZ T c Λ lam := by
  intro s y j
  rw [Level.δ]
  unfold locLF

  rw [graded_semilinear_holds, grdB_ringInverse _ _ (hΔ s j Λ), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [graded_semilinear_holds, hΔ s j (y k), SlopeTestRemainingChoices.grd_cst]

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing Formalism.MainNotions.N.Ln03

theorem zpEquiv_apply_symm {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (x : ℤ_[q]) :
    zpEquiv h (zpEquiv h.symm x) = x := by
  subst h
  rfl

theorem zpEquiv_valuation {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (x : ℤ_[q]) :
    (zpEquiv h.symm x).valuation = x.valuation := by
  subst h
  rfl

section Loc

variable {l : ℕ} [Fact l.Prime]

theorem norm_chiQ_le (P : LocPrime l) (g : GQ l) : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
  have h1 : ‖((a : ℕ) : ℚ_[l])‖ ≤ 1 := by
    rw [← PadicInt.coe_natCast]
    exact PadicInt.norm_le_one _
  have ha' : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ≤ 1 := by simpa using ha
  calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
      = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l])‖ := by rw [sub_add_cancel]
    _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ‖(a : ℚ_[l])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le ha' h1

theorem norm_chiQ (P : LocPrime l) (g : GQ l) : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
  have h1 := norm_chiQ_le P g
  have h2 := norm_chiQ_le P g⁻¹
  have hm : ((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l]) * ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hn : ‖((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l])‖ * ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, hm, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg ((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l]), norm_nonneg ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])]

theorem v_algebraMap_zp (P : LocPrime l) (LL : FinExt l) (y : ℤ_[l]) (hy : y ≠ 0) :
    P.v LL (algebraMap ℤ_[l] ↥LL.1 y) = ((y.valuation : ℕ) : WithTop ℚ) := by
  have hint : ∀ z : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 z) := fun z =>
    (P.v_O LL _).2 (Subalgebra.algebraMap_mem (OL LL) z)
  have spec := PadicInt.unitCoeff_spec hy
  set w := PadicInt.unitCoeff hy
  have hw : P.v LL (algebraMap ℤ_[l] ↥LL.1 (w : ℤ_[l])) = 0 := by
    have h1 := hint (w : ℤ_[l])
    have h2 := hint ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
    have hsum : P.v LL (algebraMap ℤ_[l] ↥LL.1 (w : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
        AddValuation.map_one]
    exact le_antisymm ((le_add_of_nonneg_right h2).trans hsum.le) h1
  conv_lhs => rw [spec]
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, hw, P.v_l, zero_add,
    nsmul_one]

end Loc

theorem uTieRec_holds (D : D7) (HW : HWOf D.loc) : UTieRec D HW := by
  intro l _ K LL h _
  obtain ⟨g0, hg0⟩ := ((HW l).W K 1 LL h.2.2).resΓ_onto ((HW l).W K 1 LL h.2.2).gam
  have hres := ((HW l).W K 1 LL h.2.2).χΓ_res g0
  rw [hg0] at hres
  have hn : ‖((((D.loc l).PD K).χ g0 : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
    rw [(D.loc l).PD_χ]
    exact norm_chiQ (D.loc l) _
  set u : ℤ_[l]ˣ := PadicInt.mkUnits hn with hu
  have hu' : ((u : ℤ_[l]) : ℚ_[l]) = ((((D.loc l).PD K).χ g0 : ℚ_[l]ˣ) : ℚ_[l]) := PadicInt.mkUnits_eq hn
  have hχ : ((((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) : ↥LL.1) =
      algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, PadicInt.algebraMap_apply, hu']
    exact hres
  refine ⟨Units.map (zpEquiv ((D.loc l).PD_p K).symm).toRingHom.toMonoidHom u, ?_, ?_⟩
  · show (zpEquiv ((D.loc l).PD_p K).symm (u : ℤ_[l]) - 1).valuation = 1
    rw [← map_one (zpEquiv ((D.loc l).PD_p K).symm), ← map_sub, zpEquiv_valuation ((D.loc l).PD_p K)]
    have hg := ((HW l).W K 1 LL h.2.2).gam_gen
    rw [(HW l).W_s K 1 LL h.2.2] at hg
    change (D.loc l).v LL ((((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) - 1) =
      ((1 : ℕ) : WithTop ℚ) at hg
    rw [hχ, ← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub] at hg
    have hne : (u : ℤ_[l]) - 1 ≠ 0 := by
      intro h0
      rw [h0, map_zero, AddValuation.map_zero] at hg
      exact WithTop.top_ne_coe hg
    rw [v_algebraMap_zp (D.loc l) LL _ hne] at hg
    exact_mod_cast hg
  · apply Subtype.ext
    show ((algebraMap ℤ_[l] ↥(OL LL) (zpEquiv ((D.loc l).PD_p K)
      (zpEquiv ((D.loc l).PD_p K).symm (u : ℤ_[l])))) : ↥LL.1) = _
    rw [zpEquiv_apply_symm, hχ]
    rfl

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.MainNotions.N.Ln03 Polynomial

theorem teichOnto_toZMod_eq_zero_iff {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← PadicInt.mem_nonunits, mem_nonunits_iff]

theorem teichOnto_norm_eq_one {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) (h : PadicInt.toZMod x ≠ 0) :
    ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one x) (not_lt.mp fun h' => h ((teichOnto_toZMod_eq_zero_iff x).mpr h'))

theorem teichOnto_holds (p : ℕ) [Fact p.Prime] : TeichOnto p := by
  intro a ha
  have hp : p.Prime := Fact.out
  set a₀ : ℤ_[p] := ((a.val : ℕ) : ℤ_[p]) with ha₀
  have hres : PadicInt.toZMod a₀ = a := by rw [ha₀, map_natCast, ZMod.natCast_zmod_val]
  set F : Polynomial ℤ_[p] := X ^ (p - 1) - 1 with hF
  have hFa : F.aeval a₀ = a₀ ^ (p - 1) - 1 := by simp [hF]
  have hF'a : F.derivative.aeval a₀ = ((p - 1 : ℕ) : ℤ_[p]) * a₀ ^ (p - 1 - 1) := by
    simp [hF, Polynomial.derivative_X_pow]
  have h1 : ‖F.aeval a₀‖ < 1 := by
    rw [← teichOnto_toZMod_eq_zero_iff, hFa, map_sub, map_pow, hres, map_one,
      ZMod.pow_card_sub_one_eq_one ha, sub_self]
  have h2 : ‖F.derivative.aeval a₀‖ = 1 := by
    apply teichOnto_norm_eq_one
    rw [hF'a, map_mul, map_pow, hres, map_natCast]
    refine mul_ne_zero ?_ (pow_ne_zero _ ha)
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, neg_ne_zero]
    exact one_ne_zero
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a₀) (by rw [h2, one_pow]; exact h1)
  rw [h2] at hza
  have hzp : z ^ (p - 1) = 1 := by
    have : F.aeval z = z ^ (p - 1) - 1 := by simp [hF]
    rw [this, sub_eq_zero] at hz
    exact hz
  have hzz : z * z ^ (p - 2) = 1 := by
    have h2p := hp.two_le
    rw [← pow_succ', show p - 2 + 1 = p - 1 by omega, hzp]
  let u : ℤ_[p]ˣ := ⟨z, z ^ (p - 2), hzz, by rw [mul_comm]; exact hzz⟩
  refine ⟨⟨u, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hzp)⟩, ?_⟩
  show PadicInt.toZMod z = a
  have h3 : PadicInt.toZMod (z - a₀) = 0 := (teichOnto_toZMod_eq_zero_iff _).mpr hza
  rw [map_sub, sub_eq_zero, hres] at h3
  exact h3

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open IsLocalRing

namespace ComplMaxPf

variable {R : Type} [CommRing R]

theorem isAdicComplete_of_pow {I J : Ideal R} (e : ℕ) (he : 1 ≤ e) (h1 : ∀ k, J ^ (e * k) ≤ I ^ k)
    (h2 : ∀ k, I ^ k ≤ J ^ k) (hI : IsAdicComplete I R) : IsAdicComplete J R := by
  have m1 : ∀ k, (J ^ (e * k) • ⊤ : Submodule R R) ≤ I ^ k • ⊤ := fun k => Submodule.smul_mono_left (h1 k)
  have m2 : ∀ k, (I ^ k • ⊤ : Submodule R R) ≤ J ^ k • ⊤ := fun k => Submodule.smul_mono_left (h2 k)
  refine { haus' := fun x hx => hI.haus' x fun k => SModEq.mono (m1 k) (hx (e * k)),
           prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.prec' (fun k => f (e * k)) fun {m n} hmn =>
    SModEq.mono (m1 m) (hf (Nat.mul_le_mul_left e hmn))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ e * n := Nat.le_mul_of_pos_left n he
  exact (hf hn).trans (SModEq.mono (m2 n) (hL n))

end ComplMaxPf

theorem complMax_holds : ComplMax := by
  intro O _ _ _ p hpm hp0 hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      rw [pow_zero, mul_one] at hu
      rw [hu] at hpm
      exact (IsLocalRing.mem_maximalIdeal _).1 hpm u.isUnit
    · exact h
  have hIk : ∀ k, Ideal.span {(p : O)} ^ k = maximalIdeal O ^ (e * k) := fun k => by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      Ideal.span_singleton_mul_left_unit (u.isUnit.pow k)]
  refine ComplMaxPf.isAdicComplete_of_pow e he (fun k => (hIk k).ge) (fun k => ?_) hc
  rw [hIk k]
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left k he)

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem levB_mem_fil (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (ζ : Rs LL PD.p s) (x : ↥(W.N T)) (k : ℤ) :
    (⟨Lb.levB T c ζ x k, Lb.mem T c ζ x k⟩ : Dc W T c) ∈ FilD W T c s (-k) := by
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pow_pos PD.hp.pos _)).1 ζ.2
  show ιV PD (LL := LL) (V := T.V) (Lb.levB T c ζ x k) ∈ FilLev W T c s (-k)
  rw [← hLb]
  exact (hP4 T hcrys c s ζ hprim).1 x k


open Classical in
theorem expN_mem_xi (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (x : ↥(W.N T)) :
    expN Lb s T c x ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) := by
  rw [xi_iff]
  intro ζ k
  have e1 : cf (expN Lb s T c x) k = coefN Lb s T c x k := rfl
  rw [e1, coefN, evaluation_expansion_at_root]
  exact levB_mem_fil hP4 hcrys hLb s ζ x k

end Formalism.MainNotions.N.Ln03.K8

end
end
