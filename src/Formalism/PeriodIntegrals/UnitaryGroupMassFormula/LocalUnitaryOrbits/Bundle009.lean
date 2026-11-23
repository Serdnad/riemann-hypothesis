module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitOfPair
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.LatCpt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TwoNeZeroV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem sig_ne (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hs
  obtain ⟨-, htc, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h4 τ x
    rw [hs, AlgHom.id_apply] at this
    rw [starRingEnd_apply]; exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 hr)

theorem fix_range (h : IsCMExt F E σ) {y : E} (hy : σ y = y) : ∃ c : F, algebraMap F E c = y := by
  apply PI.OmLocU.NormOneUnitFixedPoints.gr_fix_range <;> assumption

theorem fix_int (h : IsCMExt F E σ) (y : 𝓞 E) (hy : sigO σ y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a = y := by
  have hy' : σ (y : E) = y := by rw [← sigO_coe, hy]
  obtain ⟨c, hc⟩ := fix_range σ h hy'
  have hint : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (A := F) (B := E) , hc]
    exact y.isIntegral_coe
  refine ⟨⟨c, (mem_integralClosure_iff ℤ F).2 hint⟩, RingOfIntegers.ext ?_⟩
  exact hc

theorem qInert_holds : QInert σ J ψ v := by
  intro hstd hun hp hid
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : (IE (E := E) v).IsMaximal := hp.isMaximal (IE_ne_bot v)
  letI : Field (QE (E := E) v) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := finite_res v
  have hfr : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) = 2 := by
    rw [Ideal.finrank_quotient_map (p := v.asIdeal) (K := F) (L := E)]
    exact hstd.1.2.2.1
  have hsig : ∀ x : QE (E := E) v, sigQ σ v x = x := fun x => by rw [hid]; rfl

  have hmem : ∀ x : QE (E := E) v, (∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x + x) ∧
      ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hs : Ideal.Quotient.mk (IE (E := E) v) (sigO σ y) = Ideal.Quotient.mk _ y := by
      rw [← sigQ_mk]; exact hsig _
    have hss : sigO σ (sigO σ y) = y := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ hstd.1 _)
    obtain ⟨a, ha⟩ := fix_int σ hstd.1 (y + sigO σ y) (by rw [map_add (f := _), hss, add_comm])
    obtain ⟨b, hb⟩ := fix_int σ hstd.1 (y * sigO σ y) (by rw [map_mul, hss, mul_comm])
    refine ⟨⟨Ideal.Quotient.mk _ a, ?_⟩, ⟨Ideal.Quotient.mk _ b, ?_⟩⟩
    · rw [Ideal.Quotient.algebraMap_quotient_map_quotient, ha, map_add (f := _), hs]
    · rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hb, map_mul, hs]
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) := Module.finite_of_finrank_pos (by omega)
  haveI : Finite (QE (E := E) v) := Module.finite_of_finite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (QE (E := E) v)
  have hc : Fintype.card (QE (E := E) v) = Fintype.card (𝓞 F ⧸ v.asIdeal) ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := QE (E := E) v), hfr]
  have h1 : 1 < Fintype.card (𝓞 F ⧸ v.asIdeal) := Fintype.one_lt_card
  have hle : Fintype.card (QE (E := E) v) ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) := by
    by_cases h2 : (2 : QE (E := E) v) = 0
    · refine Fintype.card_le_of_injective (fun x => (hmem x).2.choose) fun x y hxy => ?_
      have hx : algebraMap _ _ (hmem x).2.choose = x * x := (hmem x).2.choose_spec
      have hy : algebraMap _ _ (hmem y).2.choose = y * y := (hmem y).2.choose_spec
      have hxy2 : (hmem x).2.choose = (hmem y).2.choose := hxy
      have hxy' : x * x = y * y := by rw [← hx, ← hy, hxy2]
      have h0 : (x - y) * (x - y) = 0 := by
        have : (x - y) * (x - y) = x * x + y * y - 2 * (x * y) := by ring
        rw [this, h2, zero_mul, sub_zero, hxy', ← two_mul, h2, zero_mul]
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h0)
    · refine Fintype.card_le_of_injective (fun x => (hmem x).1.choose) fun x y hxy => ?_
      have hx : algebraMap _ _ (hmem x).1.choose = x + x := (hmem x).1.choose_spec
      have hy : algebraMap _ _ (hmem y).1.choose = y + y := (hmem y).1.choose_spec
      have hxy2 : (hmem x).1.choose = (hmem y).1.choose := hxy
      have hxy' : x + x = y + y := by rw [← hx, ← hy, hxy2]
      rw [← two_mul, ← two_mul] at hxy'
      exact mul_left_cancel₀ h2 hxy'
  rw [hc] at hle
  nlinarith

end PI.OmLocU.Red
end
end

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol Formalism.L2.SG.Sub NumberField IsDedekindDomain

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem redU_of_norm (hN : Orb.NormOne σ J ψ v) (hUN : Orb.UnitNorm σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ)
    (Y : TupV (E := E) v n a) : RedU σ J ψ v Λ a Y :=
  redU_of σ J ψ v Λ (Orb.unitV_of σ J ψ v Λ hN hUN) hR a Y

theorem countU_of_res (hN : Orb.NormOne σ J ψ v) (hUN : Orb.UnitNorm σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ)
    (Y : TupV (E := E) v n a) : CountU σ J ψ v Λ a Y :=
  countU_of_bas' σ J ψ v Λ a Y (by
    classical
    intro hG
    obtain ⟨L, hLat, hL⟩ := hG.2.1
    subst Λ
    let M := latLoc (E := E) v (L : Set (Fin n → E))
    have hfg : M.FG := basLat_fg v L hLat
    have hspan : Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
      have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
      have hopen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hG.2.2.1 hfg
      rw [eq_top_iff]
      intro x _
      obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v
        (hopen.mem_nhds M.zero_mem) (fun _ : Unit => x)
      have hmem : t • x ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
        Submodule.subset_span (htx ())
      have hx : t⁻¹ • (t • x) ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
        Submodule.smul_mem _ t⁻¹ hmem
      rwa [inv_smul_smul₀ ht] at hx
    have : Submodule.IsFullLattice (Fv F v) M :=
      { toIsLattice := Submodule.IsLattice.of_fg (Fv F v) hfg, span_eq_top := hspan }
    have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 hfg
    have : Module.Free (v.adicCompletionIntegers F) M := Submodule.IsLattice.free (Fv F v) M
    let b := Module.finBasis (v.adicCompletionIntegers F) M
    let B := b.extendOfIsFullLattice (Fv F v)
    have hB (i) : B i = (b i : Fin n → Fv F v ⊗[F] E) :=
      Module.Basis.extendOfIsFullLattice_apply (Fv F v) b i
    have hmem (x : Fin n → Fv F v ⊗[F] E) : x ∈ M ↔
        ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
          x = ∑ i, (c i : Fv F v) • B i := by
      constructor
      · intro hx
        refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
        have h := congrArg (fun y : M => (y : Fin n → Fv F v ⊗[F] E)) (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h
        exact h.symm.trans (Finset.sum_congr rfl fun i _ => by rw [hB]; rfl)
      · rintro ⟨c, rfl⟩
        exact Submodule.sum_mem M fun i _ => by rw [hB]; exact M.smul_mem (c i) (b i).2
    have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have h2 : Module.finrank F E = 2 := hG.1.1.2.2.1
    have hm : Module.finrank (v.adicCompletionIntegers F) M = 2 * n := by
      have h := Module.finrank_eq_card_basis B
      rw [Fintype.card_fin] at h
      rw [← h, Module.finrank_pi_fintype]
      simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    rw [← hm]
    exact ⟨B, B.linearIndependent, hmem⟩) (resIdx_holds v)
    (redU_of_norm σ J ψ v Λ hN hUN hR a Y)

end PI.OmLocU.Red
end
end

section

noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem hR_smul_right_F (x w : Fin n → Fv F v ⊗[F] E) (c : Fv F v) :
    hR (Fv F v) σ J x (c • w) = c • hR (Fv F v) σ J x w := by
  rw [← algebraMap_smul (Fv F v ⊗[F] E) c w, hR_smul_right, Algebra.smul_def]

def perpMap {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E) where
  toFun w i := hR (Fv F v) σ J (X i) w
  map_add' x y := funext fun i => hR_add_right' σ J v (X i) x y
  map_smul' c w := funext fun i => hR_smul_right_F σ J v (X i) w c

theorem exists_perp_ne_zero (hcm : IsCMExt F E σ) {ι : Type} [Fintype ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hc : Fintype.card ι < n) : ∃ w : Fin n → Fv F v ⊗[F] E, w ≠ 0 ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0 := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have hlt : Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E) < Module.finrank (Fv F v) (Fin n → Fv F v ⊗[F] E) := by
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := perpMap σ J v X) hlt
  obtain ⟨w, hw, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨w, hne, fun i => congrFun (LinearMap.mem_ker.1 hw) i⟩

theorem primPerp_holds : PrimPerp σ J ψ v Λ := by
  classical
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨L, hLat, rfl⟩ := hL
  let M := latLoc (E := E) v (L : Set (Fin n → E))
  have hfg : M.FG := basLat_fg v L hLat
  have hspan : Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
    have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    have hopen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hsd hfg
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v
      (hopen.mem_nhds M.zero_mem) (fun _ : Unit => x)
    have hmem : t • x ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
      Submodule.subset_span (htx ())
    have hx : t⁻¹ • (t • x) ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
      Submodule.smul_mem _ t⁻¹ hmem
    rwa [inv_smul_smul₀ ht] at hx
  have : Submodule.IsFullLattice (Fv F v) M :=
    { toIsLattice := Submodule.IsLattice.of_fg (Fv F v) hfg, span_eq_top := hspan }
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 hfg
  have : Module.Free (v.adicCompletionIntegers F) M := Submodule.IsLattice.free (Fv F v) M
  let m := Module.finrank (v.adicCompletionIntegers F) M
  let b : Module.Basis (Fin m) (v.adicCompletionIntegers F) M := Module.finBasis _ _
  let B := b.extendOfIsFullLattice (Fv F v)
  have hB (i : Fin m) : B i = (b i : Fin n → Fv F v ⊗[F] E) :=
    Module.Basis.extendOfIsFullLattice_apply (Fv F v) b i
  have hmem (x : Fin n → Fv F v ⊗[F] E) : x ∈ M ↔
      ∃ c : Fin m → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • B i := by
    constructor
    · intro hx
      refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg (fun y : M => (y : Fin n → Fv F v ⊗[F] E)) (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => by
        rw [hB]
        rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem M fun i _ => by
        rw [hB]
        exact M.smul_mem (c i) (b i).2
  have hsymm := Module.Basis.equivFun_symm_apply B
  obtain ⟨w, hw0, hwp⟩ := exists_perp_ne_zero σ J v hstd.1 X hc
  set c := B.equivFun w with hcdef
  have hcw : w = ∑ i, c i • B i := by rw [← hsymm, hcdef, LinearEquiv.symm_apply_apply]
  have hcne : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw0
    rw [hcw]
    simp [h]
  obtain ⟨i0, hi0⟩ := hcne
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (c i)) hne
  have hcj : c j ≠ 0 := by
    intro h
    have h1 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h1
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))
  have hvj : Valued.v (c j) ≠ 0 := (Valuation.ne_zero_iff _).2 hcj
  set p := (c j)⁻¹ • w with hp
  have hcp : B.equivFun p = (c j)⁻¹ • c := by rw [hp, map_smul]
  have hpmem : p ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
    refine (hmem p).2 ⟨fun i => ⟨(c j)⁻¹ * c i, ?_⟩, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
      calc (Valued.v (c j))⁻¹ * Valued.v (c i) ≤ (Valued.v (c j))⁻¹ * Valued.v (c j) :=
            mul_le_mul' le_rfl (hj i (Finset.mem_univ _))
        _ = 1 := inv_mul_cancel₀ hvj
    · rw [← hsymm]
      change p = B.equivFun.symm ((c j)⁻¹ • c)
      rw [← hcp, LinearEquiv.symm_apply_apply]
  refine ⟨ϖ, hϖ, p, ⟨hpmem, fun i => ?_⟩, ?_⟩
  · rw [hp, hR_smul_right_F, hwp i, smul_zero]
  · intro hin
    rw [sc_eq, algebraMap_smul] at hin
    obtain ⟨d, hd⟩ := (hmem _).1 hin
    have hd' : ϖ⁻¹ • p = B.equivFun.symm (fun i => (d i : Fv F v)) := by rw [hsymm]; exact hd
    have hcoord := congrFun (congrArg B.equivFun hd') j
    rw [LinearEquiv.apply_symm_apply, map_smul, hcp] at hcoord
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    rw [inv_mul_cancel₀ hcj, mul_one] at hcoord
    have hint : ϖ⁻¹ ∈ v.adicCompletionIntegers F := by rw [hcoord]; exact (d j).2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hint
    have h1 : Valued.v (ϖ * ϖ⁻¹) ≤ WithZero.exp (-1 : ℤ) := by
      rw [map_mul, hv]
      calc WithZero.exp (-1 : ℤ) * Valued.v ϖ⁻¹ ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul' le_rfl hint
        _ = _ := mul_one _
    rw [mul_inv_cancel₀ hϖ0, map_one] at h1
    exact absurd h1 (by decide)

end PI.OmLocU.UnN
end
end
