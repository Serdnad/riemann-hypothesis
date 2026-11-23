module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  refine ⟨(GfC V).mul_mem hκ.1 hκ'.1, ?_, ?_⟩
  · rw [map_mul]; exact Subgroup.mul_mem _ hκ.2.1 hκ'.2.1
  · rw [map_mul, Formalism.L2.DIV.rTup_mul hκ.2.1 hκ'.2.1, hκ.2.2, hκ'.2.2]

theorem levChi_flag_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ.2.1 hκ'.2.1, Units.val_mul]

theorem levChi_flag1 (κ : GA D V) : levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_flag1]

theorem isLift_one_of_mem {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  refine ⟨hκ.1, hκ.2.1, ?_⟩
  have h : Formalism.L2.DIV.rTup β L (finE V κ) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)) := hκ.2.2
  exact Subgroup.mem_bot.mp h

theorem act_one {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : actG0 V β L 1 F = F := by
  have h1 : (1 : GA D V) ∈ levG V β (flag1L L) := Subgroup.one_mem _
  have hl := isLift_one_of_mem h1
  funext h
  rw [level_action_spec hF ⟨1, hl⟩ 1 hl h, hF 1 h1 h, levChi_flag1]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) 1
  field_simp

theorem act_hasType {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) : HasType V β (flag1L L) (actG0 V β L g F) := by
  intro k hk h
  obtain ⟨κ, hκ⟩ := hex
  have hl := isLift_one_of_mem hk
  have hkκ : IsLevelLift V β L g (k * κ) := by simpa using isLift_mul hl hκ
  rw [level_action_spec hF ⟨κ, hκ⟩ κ hκ (h * k), level_action_spec hF ⟨κ, hκ⟩ (k * κ) hkκ h, levChi_flag_mul hl hκ,
    levChi_flag1, mul_assoc h k κ]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) k
  have := levChi_ne_zero (V := V) (β := β) (flagL L) κ
  field_simp

theorem act_mul {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g g' : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) (hex' : ∃ κ, IsLevelLift V β L g' κ) :
    actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  obtain ⟨κ, hκ⟩ := hex
  obtain ⟨κ', hκ'⟩ := hex'
  have hm := isLift_mul hκ hκ'
  funext h
  rw [level_action_spec hF ⟨_, hm⟩ _ hm h, level_action_spec (act_hasType hF ⟨κ', hκ'⟩) ⟨κ, hκ⟩ κ hκ h,
    level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (h * κ), levChi_flag_mul hκ hκ', mul_assoc h κ κ', mul_inv, mul_assoc]

theorem levelGroupAction_isAction : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), LiftsExist V β L → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (actG0 V β L 1 F = F ∧ ∀ g, HasType V β (flag1L L) (actG0 V β L g F)) ∧ ∀ g g', actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  intro D V β L hL F hF
  exact ⟨⟨act_one hF, fun g => act_hasType hF (hL g)⟩, fun g g' => act_mul hF (hL g) (hL g')⟩

end GlobalTheory.FlagAction
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem mem_blockTriangular_singleBlock_of_le {κ : Type} [CommRing κ] {n r : ℕ} (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ Formalism.L2.DIV.blockTri (κ := κ) (n := n) (Formalism.L2.DIV.blk2 r) := by
  rw [Formalism.L2.DIV.mem_blockTri]
  intro i j hij
  have hi : Formalism.L2.DIV.blk2 r i = 0 := by
    unfold Formalism.L2.DIV.blk2; exact if_pos (lt_of_lt_of_le i.isLt h)
  have hj : Formalism.L2.DIV.blk2 r j = 0 := by
    unfold Formalism.L2.DIV.blk2; exact if_pos (lt_of_lt_of_le j.isLt h)
  rw [hi, hj] at hij
  exact absurd hij (lt_irrefl 0)

theorem blockDet_singleBlock_second_eq_one_of_le {κ : Type} [CommRing κ] {n r : ℕ} (h : n ≤ r) (g : GL (Fin n) κ) :
    Formalism.L2.DIV.dBlk (κ := κ) (n := n) (Formalism.L2.DIV.blk2 r) 1 g = 1 := by
  have hm := mem_blockTriangular_singleBlock_of_le (κ := κ) h g
  haveI : IsEmpty {a : Fin n // Formalism.L2.DIV.blk2 r a = 1} := by
    refine ⟨fun a => ?_⟩
    have h1 := a.2
    have h2 := a.1.isLt
    unfold Formalism.L2.DIV.blk2 at h1
    split_ifs at h1 with hlt <;> omega
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hm, Units.val_one]
  exact Matrix.det_isEmpty

theorem levG_twist_trivial_of_rank_eq :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t : ℕ) (hr : r ≤ V.rank), V.rank = r → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), levG V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B) = levG V β (datY V.rank r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) ∧ ∀ k ∈ levG V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B), levChi V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B) k = levChi V β (datY V.rank r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) k := by
  intro D V β r t hr hrk Pg Q P χ ξ
  subst hrk
  have hlev : Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) =
      Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) := by
    ext x
    simp only [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    constructor
    · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
      refine ⟨⟨h1, h2, h3, fun PP hPP => ?_⟩, h5⟩
      change PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) at hPP
      simp at hPP
    · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
      exact ⟨⟨h1, h2, h3, fun PP _ => mem_blockTriangular_singleBlock_of_le (r := V.rank) le_rfl _⟩, h5⟩
  have hfn : ∀ y, Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) y =
      Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) y := by
    intro y
    unfold Formalism.L2.DIV.levFn
    have hq : ∏ PP ∈ (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).Q,
        (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP
          (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).r) 1
            (Formalism.L2.DIV.redFn β PP y)) = 1 := by
      refine Finset.prod_eq_one fun PP _ => ?_
      have h2 := blockDet_singleBlock_second_eq_one_of_le (r := V.rank) (le_refl V.rank) (Formalism.L2.DIV.redFn β PP y)
      exact (congrArg (⇑((datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP)) h2).trans (map_one _)
    rw [hq]
    change _ = _ * ∏ PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)), _
    rw [Finset.prod_empty]
    rfl
  refine ⟨?_, fun k _ => ?_⟩
  · unfold levG
    rw [hlev]
  · unfold levChi
    rw [hfn]

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem norm_residueChar_eq_one {E : Type} [Field E] [NumberField E] (PP : Pl E) (f : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ) :
    ‖((f x : ℂˣ) : ℂ)‖ = 1 := by

  have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
  have hpow : ((f x : ℂˣ) : ℂ) ^ orderOf x = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow hx.orderOf_pos.ne'

theorem norm_levChi_flagL_eq_one :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
      ∀ κ ∈ levG V β (flagL L), ‖levChi V β (flagL L) κ‖ = 1 := by
  intro D V β L κ _

  have hP : ∀ x, ext1 (flagL L).P.H (flagL L).P.chi x = 1 := by
    intro x
    unfold ext1
    split_ifs
    · rfl
    · rfl

  rw [levChi, levFn, hP, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod,
    norm_prod, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_residueChar_eq_one PP _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_residueChar_eq_one PP _ _

end GlobalTheory
end
