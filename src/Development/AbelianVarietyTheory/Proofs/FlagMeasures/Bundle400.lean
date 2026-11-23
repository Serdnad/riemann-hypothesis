module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle357
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle389
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle358
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle381
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle352
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle321
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle034
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle391
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoprimeProjectionAdelicLatticeIntoColumns
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle394
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

@[expose] public section

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flagPairValue_invariant_unitriangularChange : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Uni A' → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' → Gval G G' = Gval F F' := by
  first | exact @GlobalTheory.LocOver.gval_uni_change | exact GlobalTheory.LocOver.gval_uni_change | (intros; apply GlobalTheory.LocOver.gval_uni_change <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem cardE (α : Type) [Nonempty α] :
    ENNReal.ofReal ((Nat.card α : ℝ)⁻¹) = ((ENat.card α : ℕ∞) : ℝ≥0∞)⁻¹ := by
  rcases finite_or_infinite α with h | h
  · have h0 : 0 < Nat.card α := Nat.card_pos
    rw [ENat.card_eq_coe_natCard, ENNReal.ofReal_inv_of_pos (by exact_mod_cast h0), ENNReal.ofReal_natCast]
    simp
  · rw [Nat.card_eq_zero_of_infinite, ENat.card_eq_top_of_infinite]
    simp


theorem rowsOrbC : GlobalTheory.TypeAsm.RowsOrbC := by
  intro D large₂ X Y u hS W HW hEmb φ hφ Λ₀ hΛ₀
  obtain ⟨e, he, heX⟩ := GlobalTheory.T.anisotropicOrthogonal_isometric_definiteModel D X u W HW hEmb
  have hlat := GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart D X u W e heX
  set M₀ := GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ₀) with hM₀
  obtain ⟨hψ, hgen, horb⟩ := GlobalTheory.T.isometry_transports_genus_orbitSum D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he φ hφ M₀
  obtain ⟨hcm, -, -, -, hf, -, -, -, -, -, -, -, hTu⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨hTp, hsp⟩ := hTu u
  have hl0 := GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hS W HW hEmb Λ₀ hΛ₀
  rw [hlat Λ₀] at hl0
  obtain ⟨hM₀i, hM₀d⟩ := GlobalTheory.T.isometry_transports_discriminantModule D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he M₀ _ hl0.1 hl0.2
  have hbs : (GlobalTheory.RowsOrb.hb X).IsSymm := ⟨fun a b => (VS D).herm.eq (a : (VS D).V) (b : (VS D).V)⟩
  have hz : GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.zb X u) = -((Tu D u : ℕ) : D.host.E) := X.zu_norm u
  have hrm := GlobalTheory.Mass.RowMean.main D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) hcm hbs (Tu D u)
    (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.Ub X u) hTp hsp hz rfl (GlobalTheory.T.anisotropicOrthogonal_totallyPositiveDefinite D X u) M₀ hM₀i hM₀d
    (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  simp only [hlat, ← hM₀, hgen]
  rw [horb, ← hf]
  refine Eq.trans ?_ hrm
  obtain ⟨hst, hinv⟩ := GlobalTheory.T.gluedLattices_stable_under_vectorStabilizer D X u M₀ (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  have hinj : ∀ a ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      ∀ b ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      GlobalTheory.RowsOrb.Lmap X u a = GlobalTheory.RowsOrb.Lmap X u b → a = b := by
    intro a ha b hb hab
    exact GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices D large₂ X Y u hS a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 1 ((one_smul (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u a)).trans hab)
  refine Eq.trans ?_ (GlobalTheory.Mass.orbSum_eq_sum_reps (GlobalTheory.RowsOrb.Gz X u) (Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X))
    {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} (fun L => φ (GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L))) hst (fun g L => hinv g L)
    (((Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀)).image (GlobalTheory.RowsOrb.Lmap X u)) ?_ ?_).symm
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    congr 1
    show ENNReal.ofReal ((Nat.card (autLz D (X.Fu u) Λ) : ℝ)⁻¹) = _
    rw [GlobalTheory.T.card_row_automorphisms_eq_lattice_stabilizer D large₂ X Y u hS Λ (Finset.mem_filter.1 hΛ).1, cardE]
  · intro L hL
    obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨hΛr, hΛg⟩ := Finset.mem_filter.1 hΛ
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.orbit_lattice_unimodular_and_primitive D large₂ X Y u hS Λ hΛr
    exact ⟨h1, h2, h3, hΛg⟩
  · intro L hL
    obtain ⟨Λ, hΛ, g, hg⟩ := GlobalTheory.T.exists_row_of_unimodular_lattice_primitive_vector D large₂ X Y u hS L hL.1 hL.2.1 hL.2.2.1
    refine ⟨GlobalTheory.RowsOrb.Lmap X u Λ, ⟨Finset.mem_image.2 ⟨Λ, Finset.mem_filter.2 ⟨hΛ, ?_⟩, rfl⟩, g, hg⟩, ?_⟩
    · have := hst g⁻¹ L hL
      erw [← hg, inv_smul_smul] at this
      exact this.2.2.2
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.1 hy
      congr 1
      exact GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices D large₂ X Y u hS Λ' (Finset.mem_filter.1 hΛ').1 Λ hΛ (g⁻¹ * g') (by erw [mul_smul, hg', ← hg, inv_smul_smul])

end GlobalTheory.RowsOrb
end

section

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main
variable {D : D7} {X : HidaSetting D}

theorem stab_of_fix' (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  · have h' : (F0 X u).e (Fin.last _) = (X.Fu u).z := fv_last (lf D (X.Fu u)).fl
    have := hfix (Fin.last _)
    rw [h'] at this
    exact this

theorem fix_X (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a x = x := by
  intro x hx
  have h : Set.EqOn (⇑(a : (VS D).V →ₗ[D.host.E] (VS D).V)) (⇑(LinearMap.id : (VS D).V →ₗ[D.host.E] (VS D).V))
      (Set.range (X.Fu u).e) := by
    rintro _ ⟨i, rfl⟩
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  simpa using LinearMap.eqOn_span h hx

theorem perp_pres (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∀ y ∈ perpS (VS D) (X.Fu u).X, a y ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy x hx
  rw [← fix_X u hfix x hx, hi x y]
  exact hy x hx

theorem ind_exists (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X) (hx : a x.1 ∈ perpS (VS D) (X.Fu u).X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨a x.1, hx⟩ := by
  let f : perpS (VS D) (X.Fu u).X →ₗ[D.host.E] perpS (VS D) (X.Fu u).X :=
    (a : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (perp_pres u hi hfix)
  let q := (X.Fu u).X.comap (perpS (VS D) (X.Fu u).X).subtype
  have hq : q ≤ q.comap f := by
    intro x hx
    simp only [q, Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    show a x.1 ∈ (X.Fu u).X
    rw [fix_X u hfix x.1 hx]; exact hx
  refine ⟨Submodule.mapQ q q f hq, fun x hx => ?_⟩
  rw [Submodule.mapQ_apply]
  rfl

end Main
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Main2
variable {D : D7} {X : HidaSetting D}

theorem symm_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a.symm x = x :=
  fun x hx => a.symm_apply_eq.2 (fix_X u hfix x hx).symm

theorem aut_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (y : (VS D).V) : a.symm y ∈ Λ ↔ y ∈ Λ := by
  rw [← GlobalTheory.LoopC.FrEqv.mem_gmap (Λ := Λ) a y, hga]

theorem nlam_of_same (u : D.what₂.Word) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hia : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hib : b ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (hgb : Formalism.HermitianLatticesTheory.gmap b Λ = Λ)
    (hfa : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) (hfb : ∀ c, b ((F0 X u).e c) = (F0 X u).e c)
    (hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, b x - a x ∈ (X.Fu u).X) :
    a⁻¹ * b ∈ NLam Λ (lf D (X.Fu u)) := by
  have happ : ∀ x, (a⁻¹ * b) x = a.symm (b x) := fun x => rfl
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hia) hib, ?_⟩,
    fun j x hx => ?_, fun x hx => ?_⟩
  · ext y
    rw [GlobalTheory.LoopC.FrEqv.mem_gmap]
    have : (a⁻¹ * b).symm y = b.symm (a y) := by
      apply (a⁻¹ * b).injective
      rw [LinearEquiv.apply_symm_apply, happ, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    rw [this, aut_iff hgb]
    have h2 := aut_iff hga (a y)
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  · have hX : x ∈ (X.Fu u).X := by
      have hle : Xflag (lf D (X.Fu u)) (j + 1) ≤ (X.Fu u).X :=
        Submodule.span_mono (by rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)
      exact hle hx
    rw [happ, fix_X u hfb x hX, symm_fix u hfa x hX, sub_self]
    exact zero_mem _
  · have hp : x ∈ perpS (VS D) (X.Fu u).X := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
      exact fun y hy => hx y hy
    have e : (a⁻¹ * b) x - x = a.symm (b x - a x) := by
      rw [happ, map_sub, LinearEquiv.symm_apply_apply]
    rw [e, symm_fix u hfa _ (hsame x hp)]
    exact hsame x hp

end Main2
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fibCardC : FibCardC := by
  intro D large₂ X Y u hStd t₀ s hs
  show (s.card : ℝ) * ((Nat.card (autLz D (X.Fu u) t₀.lam') : ℝ))⁻¹ ≤ 1
  by_cases hfin : Finite (autLz D (X.Fu u) t₀.lam')
  swap
  · have : Infinite (autLz D (X.Fu u) t₀.lam') := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite]; simp
  have H : ∀ t : s, ∃ a : (VS D).V ≃ₗ[D.host.E] (VS D).V, a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      Formalism.HermitianLatticesTheory.gmap a t₀.lam' = t₀.lam' ∧ (∀ c, a ((F0 X u).e c) = (F0 X u).e c) ∧ t₀.lam' = t.1.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u)), t.1.lin = n * t₀.lin * a * n' := by
    intro t
    obtain ⟨hl, n, a, hn, ha, hga, hfa, n', hn', he⟩ :=
      GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hStd t₀ t.1 (hs t.1 t.2).1 (hs t.1 t.2).2
    exact ⟨a, ha, hga, hfa, hl, n, hn, n', hn', he⟩
  choose A hA using H
  have Hφ : ∀ t : s, ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X)
      (hx : A t x.1 ∈ perpS (VS D) (X.Fu u).X), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨A t x.1, hx⟩ :=
    fun t => ind_exists u (hA t).1 (hA t).2.2.1
  choose Φ hΦ using Hφ
  have hmem : ∀ t, Φ t ∈ autLz D (X.Fu u) t₀.lam' :=
    fun t => ⟨A t, stab_of_fix' u (hA t).1 (hA t).2.2.1, (hA t).2.1, hΦ t⟩
  let f : s → autLz D (X.Fu u) t₀.lam' := fun t => ⟨Φ t, hmem t⟩
  have hinj : Function.Injective f := by
    intro t₁ t₂ h12
    have hΦe : Φ t₁ = Φ t₂ := congrArg Subtype.val h12
    obtain ⟨hi1, hg1, hf1, hl1, n₁, hn₁, n₁', hn₁', he1⟩ := hA t₁
    obtain ⟨hi2, hg2, hf2, hl2, n₂, hn₂, n₂', hn₂', he2⟩ := hA t₂
    have hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, A t₂ x - A t₁ x ∈ (X.Fu u).X := by
      intro x hx
      have p1 := perp_pres u hi1 hf1 x hx
      have p2 := perp_pres u hi2 hf2 x hx
      have k1 := hΦ t₁ ⟨x, hx⟩ p1
      have k2 := hΦ t₂ ⟨x, hx⟩ p2
      rw [hΦe, k2] at k1
      have := (Submodule.Quotient.eq _).1 k1
      rw [Submodule.mem_comap] at this
      simpa using this
    have hm := nlam_of_same u hi1 hi2 hg1 hg2 hf1 hf2 hsame
    apply Subtype.ext
    apply GlobalTheory.TypeAsm.eqC_holds D X Y u t₁.1 t₂.1
    · rw [← (hs t₁.1 t₁.2).1, ← (hs t₂.1 t₂.2).1]
    · rw [← hl1, ← hl2]
    · refine ⟨n₂ * n₁⁻¹, ?_, n₁'⁻¹ * ((A t₁)⁻¹ * A t₂) * n₂', ?_, ?_⟩
      · rw [← (hs t₁.1 t₁.2).1]; exact Formalism.L2.SG.Pf.nlam_mul hn₂ (Formalism.L2.SG.Pf.nlam_inv hn₁)
      · rw [← hl1]; exact Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_inv hn₁') hm) hn₂'
      · rw [he1, he2]; group
  have hcard : Nat.card s ≤ Nat.card (autLz D (X.Fu u) t₀.lam') := Nat.card_le_card_of_injective f hinj
  have hs' : Nat.card s = s.card := by simp
  rw [hs'] at hcard
  rcases Nat.eq_zero_or_pos (Nat.card (autLz D (X.Fu u) t₀.lam')) with h0 | hpos
  · rw [h0]; simp
  · have hp : (0 : ℝ) < Nat.card (autLz D (X.Fu u) t₀.lam') := by exact_mod_cast hpos
    rw [← div_eq_mul_inv, div_le_one hp]; exact_mod_cast hcard

end GlobalTheory.TypeAsm.FibCard
end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelic_columns_lattice_divisible_by_level_away_chosen : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ y ∈ hat D.host.F (Mq wt), ∃ z ∈ hat D.host.F (Mq wt), (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  first | exact @GlobalTheory.St.G.FrameFull.eps_full | exact GlobalTheory.St.G.FrameFull.eps_full | (intros; apply GlobalTheory.St.G.FrameFull.eps_full <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelic_embedding_basis_lies_in_module : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), InMod X.B.I X.B.g (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) (embA X wt ιA y) → InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  first | exact @GlobalTheory.St.G.TransportCong.inModL_of_inMod_embA | exact GlobalTheory.St.G.TransportCong.inModL_of_inMod_embA | (intros; apply GlobalTheory.St.G.TransportCong.inModL_of_inMod_embA <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u F wt J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, J ξ = p := by
  first | exact @GlobalTheory.St.coefficient_map_exists_onto | exact GlobalTheory.St.coefficient_map_exists_onto | (intros; apply GlobalTheory.St.coefficient_map_exists_onto <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transport_rational_points_stabiliser_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) → (∀ γ : Gam X u, ∃ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ∧ (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ (∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ γ : Gam X u, (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E), (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g → sTil X wt (iotaI X u γ : X.B.I.Ginf) = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1 := by
  first | exact @GlobalTheory.transport_rational_points | exact GlobalTheory.transport_rational_points | (intros; apply GlobalTheory.transport_rational_points <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transported_type_vectors_dual_mod_level : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) → ∀ i j, ∃ t ∈ OAd D.host.F D.host.E, hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) (bd i) (b j) - (if i = j then ιA X.ew else 0) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) * t := by
  first | exact @GlobalTheory.St.G.DualMod.dual_mod | exact GlobalTheory.St.G.DualMod.dual_mod | (intros; apply GlobalTheory.St.G.DualMod.dual_mod <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transported_type_vectors_fixed_by_chosen_places_idempotent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, b i = ιA X.ew • b i) ∧ ∀ i, bd i = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) • bd i := by
  first | exact @GlobalTheory.St.G.FrameEps.beps | exact GlobalTheory.St.G.FrameEps.beps | (intros; apply GlobalTheory.St.G.FrameEps.beps <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columns_character_eq_linked_frame_character : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ hk : h ∈ Ku X u hK, ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = Fr.chi y.1 := by
  first | exact @GlobalTheory.St.G.ColChar.psiK_eq_chi | exact GlobalTheory.St.G.ColChar.psiK_eq_chi | (intros; apply GlobalTheory.St.G.ColChar.psiK_eq_chi <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_coprime_projection_adelic_lattice_into_columns : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] ∧ (∀ y, ∃ x, p y = embA X wt ιA x) ∧ (∀ x, p (embA X wt ιA x) = embA X wt ιA x) ∧ (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) ∧ (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) ∧ p (incl X.B.I (X.zR u)) = 0 ∧ ∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧ InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a))) → InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u)) → (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ mL X.B.I X.B.g := by
  first | exact @GlobalTheory.St.G.g_proj | exact GlobalTheory.St.G.g_proj | (intros; apply GlobalTheory.St.G.g_proj <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselExteriorPower_constant_bound_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  first | exact @GlobalTheory.GapWedgeKappaL.kappa_bound | exact GlobalTheory.GapWedgeKappaL.kappa_bound | (intros; apply GlobalTheory.GapWedgeKappaL.kappa_bound <;> assumption)
end
