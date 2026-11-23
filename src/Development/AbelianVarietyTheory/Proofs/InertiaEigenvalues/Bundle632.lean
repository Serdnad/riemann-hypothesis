module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle154
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle179
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.CoordBaseChange
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle254
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle006
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle012
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle008
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle014

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

noncomputable section

namespace GlobalTheory.FrobLiftUnr

variable {l : ℕ} [Fact l.Prime]

theorem qK_bot : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (⊥ : IntermediateField ℚ_[l] (Om l)) = l := by
  have hK : FiniteDimensional ℚ_[l] (⊥ : IntermediateField ℚ_[l] (Om l)) := inferInstance
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.eK_mul_fK l ⊥ hK
  rw [IntermediateField.finrank_bot] at h
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK l ⊥ hK, Nat.eq_one_of_mul_eq_one_left h, pow_one]

theorem exists_frob : ∃ Φ : GQ l, ∀ x : Om l, ‖x‖ ≤ 1 → ‖Φ x - x ^ l‖ < 1 := by
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l)))
    inferInstance
  refine ⟨σ.restrictScalars ℚ_[l], fun x hx => ?_⟩
  have h := hσ x hx
  rw [qK_bot] at h
  exact h

theorem mem_GK_qlExt (Φ : GQ l) : Φ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  unfold GK
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact Φ.commutes r

theorem max_unramified_le_unramified_ext (K' : FinExt l) :
    K0 K' ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l ((⊥ : IntermediateField ℚ_[l] (Om l))) := by
  refine (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l).trans ?_
  unfold MaximalUnramifiedExtension
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨m, -, hm, hx⟩
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow inferInstance hm hx

theorem max_unramified_eq_adjoin_roots (K' : FinExt l) : ∃ d : ℕ, 0 < d ∧
    K0 K' = IntermediateField.adjoin ℚ_[l] {ζ : Om l | ζ ^ (l ^ d - 1) = 1} := by
  have hQ : FiniteDimensional ℚ_[l] ((⊥ : IntermediateField ℚ_[l] (Om l))) := inferInstance
  have hK' : FiniteDimensional ℚ_[l] K'.1 := K'.2
  have hM : FiniteDimensional ℚ_[l] (K0 K') :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finDim_of_le l hK' (inf_le_left : K0 K' ≤ K'.1)
  obtain ⟨N, hN, hMN⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_le_Kn_of_le_Kur hQ hM (max_unramified_le_unramified_ext K')
  have hbot : (⊥ : IntermediateField ℚ_[l] (Om l)) ≤ K0 K' := bot_le
  have hd := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_pos (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l))) hM
  have heq := ReciprocityTheory.DiscreteGroups.LocalClassField.eq_Kn_of_norm l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hbot hd
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_eq_degLK_mul hbot hM)
    (fun x hx => ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hN (hMN hx))
  refine ⟨_, hd, heq.trans ?_⟩
  unfold ReciprocityTheory.DiscreteGroups.LocalClassField.Kn
  rw [qK_bot]
  exact bot_sup_eq _

theorem not_dvd_pow_sub_one {d : ℕ} (hd : 0 < d) : ¬ l ∣ l ^ d - 1 := by
  intro h
  have hp : l.Prime := Fact.out
  have h1 : l ∣ l ^ d := dvd_pow_self l hd.ne'
  have h2 : 1 ≤ l ^ d := Nat.one_le_pow _ _ hp.pos
  have h3 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem frobenius_lift_eq_on_maxUnramifiedSubfield (K' : FinExt l) (Φ : GQ l) (hΦ : ∀ x : Om l, ‖x‖ ≤ 1 → ‖Φ x - x ^ l‖ < 1)
    (σ : ↥(K0 K') →ₐ[ℚ_[l]] ↥(K0 K'))
    (hσ : ∀ x : ↥(K0 K'), ‖((x : ↥(K0 K')) : Om l)‖ ≤ 1 →
      ‖((σ x : ↥(K0 K')) : Om l) - ((x : ↥(K0 K')) : Om l) ^ l‖ < 1)
    (c : ↥(K0 K')) : Φ (c : Om l) = ((σ c : ↥(K0 K')) : Om l) := by
  obtain ⟨d, hd, hM⟩ := max_unramified_eq_adjoin_roots K'
  have hm := not_dvd_pow_sub_one (l := l) hd
  have hm0 : l ^ d - 1 ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero l)
  have key : ((Φ.toAlgHom.restrictScalars ℚ_[l]).comp (K0 K').val : ↥(K0 K') →ₐ[ℚ_[l]] Om l) =
      (K0 K').val.comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] hM fun ζ hζ => ?_
    set z : ↥(K0 K') := ⟨ζ, hM ▸ IntermediateField.subset_adjoin ℚ_[l] _ hζ⟩ with hz
    change Φ ζ = ((σ z : ↥(K0 K')) : Om l)
    have hζ' : ζ ^ (l ^ d - 1) = 1 := hζ
    have hn : ‖ζ‖ = 1 := ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ'
    have h1 : (Φ ζ) ^ (l ^ d - 1) = 1 := by rw [← map_pow, hζ', map_one]
    have hz1 : z ^ (l ^ d - 1) = 1 := Subtype.ext hζ'
    have h2 : ((σ z : ↥(K0 K')) : Om l) ^ (l ^ d - 1) = 1 := by
      rw [← IntermediateField.coe_pow, ← map_pow, hz1, map_one]; rfl
    by_contra hne
    have e := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_sub_eq_one_of_pow_eq_one l hm h1 h2 hne
    have a1 := hΦ ζ hn.le
    have a2 := hσ z hn.le
    have : ‖Φ ζ - ((σ z : ↥(K0 K')) : Om l)‖ < 1 := by
      have eq : Φ ζ - ((σ z : ↥(K0 K')) : Om l) =
          (Φ ζ - ζ ^ l) + (ζ ^ l - ((σ z : ↥(K0 K')) : Om l)) := by ring
      rw [eq]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt a1 ?_)
      rw [norm_sub_rev]; exact a2
    exact absurd e this.ne
  exact congrArg (fun f : ↥(K0 K') →ₐ[ℚ_[l]] Om l => f c) key

end GlobalTheory.FrobLiftUnr

namespace GlobalTheory.FrobLiftUnr

theorem exists_frob_inv_mul_mem_iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Fr : Gl l), (pc Pl h hN hF hS).IsFrob Fr → ∃ Φ : Gl l, (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Φ : GQ l) x - x ^ l‖ < 1) ∧ Φ⁻¹ * Fr ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl AI _ K' h hN hF hS Fr hFr
  obtain ⟨Φ, hΦ⟩ := exists_frob (l := l)
  refine ⟨⟨Φ, mem_GK_qlExt Φ⟩, fun x _ hx => hΦ x hx, ?_⟩
  intro c
  have hc := hFr c
  have key := frobenius_lift_eq_on_maxUnramifiedSubfield K' Φ hΦ (Pl.PD K').σ (Pl.PD_σ K') c
  have hc' : Pl.actQ Φ (algebraMap ↥(K0 K') Pl.R.B c) =
      algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) :=
    Pl.actQ_Kur Φ ⟨(c : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) c.2⟩
      ⟨(((Pl.PD K').σ c : ↥(K0 K')) : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) ((Pl.PD K').σ c).2⟩ key
  change (Pl.PD _).actB Fr _ = algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) at hc
  change (Pl.PD _).actB _ _ = _
  rw [Pl.PD_actB] at hc ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, AlgEquiv.mul_apply]
  change Pl.actQ Φ⁻¹ (Pl.actQ (Fr : GQ l) _) = _
  rw [hc, ← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]

end GlobalTheory.FrobLiftUnr
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem mem_DdRE_qlExt {l : ℕ} [Fact l.Prime] (Pl : LocPrime l) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] (ρ : Representation LL ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)) V)
    (τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] LL) (y : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hy : y ∈ DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    y ∈ DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ τ := by
  refine Submodule.mem_inf.mpr ⟨hy, ?_⟩
  clear hy
  refine Submodule.mem_iInf _ |>.mpr fun c => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp c.2
  obtain rfl : c = algebraMap ℚ_[l] _ r := Subtype.ext hr.symm
  rw [AlgHom.commutes, algebraMap_smul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      LinearMap.mulLeft_apply]
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      TensorProduct.tmul_smul]
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]

theorem isJumpV_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  intro l _ Pl LL T F _ i x hfix hi hni τ
  have h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ F.1 := bot_le
  have hE : ∀ u, DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u =
      DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u := by
    intro u
    refine le_antisymm (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ fun y hy => ?_)
    exact mem_DdRE_qlExt Pl T.ρ τ y hy
  unfold IsJumpV FildR
  rw [hE, hE]
  refine (GlobalTheory.JumpDescent.jump_iff l Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F LL h T i).mp ?_
  intro heq
  have hxD : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) := by
    refine (GlobalTheory.JumpDescent.mem_DdR Pl F _ x).mpr fun g => ?_
    rw [GlobalTheory.JumpDescent.actVdR_comp Pl h]
    exact hfix _ g.2
  have hx : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
      FilV (Pl.PD F) (LL := ↥LL.1) (V := T.V) i :=
    ⟨hxD, by rw [GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hi⟩
  rw [← heq] at hx
  exact hni (by rw [← GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hx.2)

end GlobalTheory.BKGal
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InerQl

theorem root_eq_of_near {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m)
    {ζ η : Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  first
  | exact @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | (apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one ..)

theorem IK_fixes_Kur {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) {g : ↥(GK K)} (hg : g ∈ IK K)
    {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : (g : GQ l) c = c := by
  let Fx : Subgroup ↥(GK K) :=
    { carrier := {g | ∀ c ∈ MaximalUnramifiedExtension l, (g : GQ l) c = c}
      one_mem' := fun c _ => rfl
      mul_mem' := fun {a b} ha hb c hc => by
        show (a : GQ l) ((b : GQ l) c) = c
        rw [hb c hc, ha c hc]
      inv_mem' := fun {a} ha c hc => by
        show ((a : GQ l)⁻¹) c = c
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← ha c hc]
        exact AlgEquiv.symm_apply_apply _ _ }
  have hle : IK K ≤ Fx := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ c hc
    unfold MaximalUnramifiedExtension at hc
    induction hc using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm, hlm, hxm⟩ := hx
      have hxn : ‖x‖ ≤ 1 := by
        have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
        exact ((pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 this).le
      exact root_eq_of_near hm hlm hxm (by rw [← map_pow, hxm, map_one]) (hσ x hxn)
    | algebraMap x => exact (σ : GQ l).commutes x
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  exact hle hg c hc

theorem IK_mem_Iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → g ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl K' h hN hF hS g hg c
  show (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c
  rw [Pl.PD_actB]
  have hc : (c : Om l) ∈ MaximalUnramifiedExtension l := (IntermediateField.mem_inf.1 c.2).2
  exact Pl.actQ_Kur (g : GQ l) ⟨c, hc⟩ ⟨c, hc⟩ (IK_fixes_Kur _ hg hc)

end GlobalTheory.InerQl
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Algebra Qp LL] [Field LL'] [Algebra Qp LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem isCrys_transport {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have key := PI.CoefExt.finrank_iInf_ker_equiv
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp B)) (actVB PD ρ) (actVB PD ρ') (fun g x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul v c => simp [actVB, he])
  unfold IsCrys at h ⊢
  rw [← e.finrank_eq, ← h]
  exact key

theorem isCrys_matrix_ext (f : LL →ₐ[Qp] LL') {k : ℕ} (b : Module.Basis (Fin k) LL V)
    (ρ : Representation LL G V) (h : IsCrys PD ρ) :
    IsCrys PD (CJ.rep ((f.mapMatrix : Matrix (Fin k) (Fin k) LL →ₐ[Qp]
      Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ))) := by
  letI : TopologicalSpace G := ⊥
  have h1 : IsCrys PD (CJ.rep ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)) := by
    refine isCrys_transport PD b.equivFun (fun g v => ?_) h
    change _ = (LinearMap.toMatrix b b (ρ g)).mulVec (b.repr v)
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl
  exact PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange PD f _ h1

end Gen

theorem isPotCrys_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b), (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).IsPotCrys (extLat hL T b hb).ρ := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb hT
  exact isCrys_matrix_ext (pc Pl h hN hF hS).PD' (incl hL) b ((pc Pl h hN hF hS).resH T.ρ) hT

end GlobalTheory.BaseCoef
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem bot_emb_factor {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (hL : LL.1 ≤ LL'.1)
    (τ' : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL'.1) :
    ∃ τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1, τ' = (incl hL).comp τ := by
  refine ⟨IntermediateField.inclusion (bot_le : (⊥ : IntermediateField ℚ_[l] _) ≤ LL.1), ?_⟩
  refine AlgHom.ext fun x => ?_
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 (show x.1 ∈ (⊥ : IntermediateField ℚ_[l] _) from x.2)
  have hx : x = algebraMap ℚ_[l] _ c := Subtype.ext hc.symm
  rw [hx, AlgHom.commutes, AlgHom.commutes]




theorem jumpsInV_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb U H τ' a ha
  obtain ⟨τ, rfl⟩ := bot_emb_factor hL τ'
  refine H τ a ?_
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr (pc Pl h hN hF hS).PD b.equivFun
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf_equiv b T.ρ) τ a
  have e2 := Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general (pc Pl h hN hF hS).PD (incl hL)
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf b T.ρ) τ a
  exact e1.2 (e2.2 ha)

end GlobalTheory.BaseCoef
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

open scoped Pointwise

namespace GlobalTheory.BKGal.ContNear

theorem sub_mem_pow_smul_lattice_eventually :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (t : T.V), t ∈ T.L.T → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ t' ∈ T.L.T, T.ρ g t - t = ((l : ↥LL.1) ^ m) • t' := by
  intro l _ LL T t _ m
  have hO := GlobalTheory.HTW.Rec.goodO_finExt_integers l LL
  have hT : IsOpen (T.L.T : Set T.V) := GlobalTheory.Cyc.locLat_isOpen hO T
  have hc : ((l : ↥LL.1) ^ m) ≠ 0 := by
    refine pow_ne_zero _ ?_
    have h1 : (l : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l]) := by simp
    rw [h1, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hU : IsOpen (((l : ↥LL.1) ^ m) • (T.L.T : Set T.V)) := hT.smul₀ hc
  haveI := hO.2.2.2.1
  haveI := IsModuleTopology.topologicalAddGroup (↥LL.1) T.V
  have hf : Continuous fun g : Gl l => T.ρ g t - t := (T.cont t).sub continuous_const
  have h0 : (fun g : Gl l => T.ρ g t - t) 1 ∈ ((l : ↥LL.1) ^ m) • (T.L.T : Set T.V) := by
    simp only [map_one, Module.End.one_apply, sub_self]
    exact ⟨0, T.L.T.zero_mem, smul_zero _⟩
  filter_upwards [hf.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with g hg
  obtain ⟨t', ht', he⟩ := hg
  exact ⟨t', ht', he.symm⟩

end GlobalTheory.BKGal.ContNear
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ExtJumps

open Module Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence



theorem jumps_of_ses {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (Tt : LocTied l P AI)
    {K LL : FinExt l} (T T₁ T₂ : Lat K LL) (f : T.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V)
    (hses : IsSES f g) (hdr0 : IsDR (P.PD K) T.ρ) (hdr1 : IsDR (P.PD K) T₁.ρ) (hdr2 : IsDR (P.PD K) T₂.ρ)
    (τ : Emb K LL) (h2 : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₂.ρ τ b) = if b ≤ 0 then 1 else 0)
    (U : Set ℤ) (hU : (0 : ℤ) ∈ U) (hJ : JumpsInV (P.PD K) T.ρ τ U) : JumpsInV (P.PD K) T₁.ρ τ U := by
  have := K.2
  have := LL.2
  have hfin : ∀ b, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) := by
    intro b
    haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI Tt K LL T₁.V T₁.ρ).1
    exact Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_left)
  have key : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) =
      finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) + if b ≤ 0 then 1 else 0 := by
    intro b
    have hs : StrictAt P K LL := GlobalTheory.DRFil.strictAt Tt K LL
    have hs2 := hs T T₁ T₂ f g hses hdr0 hdr1 hdr2 τ b
    unfold SubSES at hs2
    obtain ⟨k₀, k₁, k₂⟩ := hs2
    haveI := hfin b
    have h := GlobalTheory.CrysExt.finrank_add_of_exact (LL := ↥LL.1) (mapdR P f) (mapdR P g) (FildR (P.PD K) T.ρ τ b)
      (FildR (P.PD K) T₁.ρ τ b) (FildR (P.PD K) T₂.ρ τ b) k₀ (Submodule.ext k₁) (Submodule.ext k₂)
    have h3 := h2 b
    omega
  intro b hb
  by_contra hbU
  have hTb : FildR (P.PD K) T.ρ τ (b + 1) = FildR (P.PD K) T.ρ τ b := by
    by_contra h
    exact hbU (hJ b h)
  have hb0 : b ≠ 0 := by rintro rfl; exact hbU hU
  apply hb
  haveI := hfin b
  have hle : FildR (P.PD K) T₁.ρ τ (b + 1) ≤ FildR (P.PD K) T₁.ρ τ b :=
    GlobalTheory.DRFil.FildR_antitone (P.PD K) T₁.ρ τ (Int.le_add_one le_rfl)
  have e3 : finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) :=
    congrArg (fun S : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) => finrank ↥LL.1 ↥S) hTb
  have e1 := key (b + 1)
  have e2 := key b
  have hr : finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) := by
    have h4 : (if b + 1 ≤ 0 then 1 else 0 : ℕ) = if b ≤ 0 then 1 else 0 := by
      split_ifs <;> omega
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle hr

theorem jumps_extLat : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (T : QLat LL) (U : Finset ℤ), (0 : ℤ) ∈ U → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)) → ∀ z : ↥(latticeCocycles T.L), IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ → ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z).ρ τ (U : Set ℤ) := by
  intro l _ a e _ _ ϖ LL _ _ Pl AI hstd T U hU hT hJ z hz τ
  obtain ⟨Tt⟩ := hstd
  have hK : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ (ϖ.field a).1 := bot_le
  have := (Formalism.MainNotions.ElementDenominator.qlExt l).2
  have := LL.2
  have hdr0 := GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL T (ϖ.field a) hK hT
  have hdr1 := GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL
    (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a) hK hz
  have hext := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt T.ρ ⟨(z : Gl l → T.V), z.2.1⟩
  refine jumps_of_ses Tt T (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (unitLat (Gl l))
    (LinearMap.inl ↥LL.1 T.V ↥LL.1) (LinearMap.snd ↥LL.1 T.V ↥LL.1)
    ⟨hext.1.2.2.2.1, hext.1.2.2.2.2, hext.1.1, hext.1.2.1, hext.1.2.2.1⟩ hdr0 hdr1
    (GlobalTheory.CrysExt.isDR_trivial (G := Gl l) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1)) τ
    (fun b => GlobalTheory.CrysExt.finrank_fildR_trivial (G := Gl l) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) τ b) _ hU (hJ τ)

end GlobalTheory.ExtJumps
end
