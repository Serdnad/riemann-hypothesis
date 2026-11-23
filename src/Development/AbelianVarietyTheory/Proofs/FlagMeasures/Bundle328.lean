module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselQuotientMassEqConstMulNormSqTranslates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle323
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle318
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle161
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagClassMeasureBoundLatticeStabiliser
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsExactGramFrameInTermClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_l2SG_translates_eq_const_mul_norm_sq : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B : R.H → Wp) (w : R.H), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π B → w ∈ R.sm → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → ∃ c : ℝ, 0 ≤ c ∧ ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = ENNReal.ofReal (c * ‖v‖ ^ 2) := by
  first | exact @GlobalTheory.BesselIsometry.besselQuotientMass_eq_const_mul_norm_sq_translates | exact GlobalTheory.BesselIsometry.besselQuotientMass_eq_const_mul_norm_sq_translates | (intros; apply GlobalTheory.BesselIsometry.besselQuotientMass_eq_const_mul_norm_sq_translates <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

theorem iota_int_cofinite {D : D7} (Z : LocDat D) (x : D.host.E) :
    {p : PlF D | (D.s.atP p).ιE x ∉ (Z.M p).L.O}.Finite := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = y.natAbs := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by rw [hn]; exact Int.natAbs_ne_zero.2 hy0
  have hint' : IsIntegral ℤ ((n : D.host.E) * x) := by
    rcases Int.natAbs_eq y with h | h <;> rw [← hn] at h
    · have e : y • x = (n : D.host.E) * x := by
        rw [zsmul_eq_mul, h, Int.cast_natCast]
      rw [← e]; exact hint
    · have e : y • x = -((n : D.host.E) * x) := by
        rw [zsmul_eq_mul, h, Int.cast_neg, Int.cast_natCast, neg_mul]
      have := hint.neg
      rw [e, neg_neg] at this
      exact this
  let w : 𝓞 D.host.E := ⟨(n : D.host.E) * x, hint'⟩
  have hfin : {p : PlF D | Loc.resChar p ∣ n}.Finite := by
    have hne : (Ideal.span {((n : ℕ) : 𝓞 D.host.F)} : Ideal (𝓞 D.host.F)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hn0
    refine (Ideal.finite_factors hne).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, bt_natCast_mem_iff]
    exact hp
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  by_contra hnd
  apply hp
  obtain ⟨_, w', hw'O, hw'⟩ := bt_nat_unit Z p n hnd
  have hwO := bt_iota_int Z p w
  have e : (D.s.atP p).ιE x = w' * (D.s.atP p).ιE (w : D.host.E) := by
    show _ = w' * (D.s.atP p).ιE ((n : D.host.E) * x)
    rw [map_mul, map_natCast, ← mul_assoc, hw', one_mul]
  rw [e]
  exact Subring.mul_mem _ hw'O hwO

theorem tri_scaled : ∀ (D : D7) (Z : LocDat D), ∀ (f g : Fin (D.R.rS + 1) → (VS D).V)
    (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Chg f A g →
    ∃ Ap : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ p, Uni (Ap p) ∧ Chg (scaled Z p f) (Ap p) (scaled Z p g)) ∧
      {p : PlF D | ¬ ∀ a b, Ap p a b ∈ (Z.M p).L.O}.Finite := by
  intro D Z f g A hA hg
  refine ⟨fun p a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b), ?_, ?_⟩
  · intro p
    refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
    · simp [hA.1 a b hab]
    · show Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a * (D.s.atP p).ιE (A a a) = 1
      rw [hA.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)]
    · simp only [scaled]

      rw [hg b, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [baseChange_smul₂, smul_smul, smul_smul]
      congr 1
      have h := Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)
      linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h
  · have hD := locDiffC_holds D Z
    refine (Set.Finite.biUnion (Set.finite_univ (α := Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
      (fun ab _ => iota_int_cofinite Z (A ab.1 ab.2))).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, not_forall] at hp
    obtain ⟨a, b, hab⟩ := hp
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, exists_true_left]
    refine ⟨(a, b), ?_⟩
    intro hι
    apply hab
    rcases lt_or_ge b a with h | h
    · simp [hA.1 a b h]
    · obtain ⟨k, hk, hkb⟩ := bt_frFac_step Z p hD a b h
      have e : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b) =
          k * (D.s.atP p).ιE (A a b) := by
        rw [hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a), one_mul]
      rw [e]
      exact Subring.mul_mem _ hk hι

end GlobalTheory.LocOver
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMinor

theorem leadMinor_atBase : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS),
    AtBase Z p F F' Tn T'n P → ∀ l : ℕ, P.Dm l =
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  intro D Z p T T' F F' Tn T'n P hP l
  obtain ⟨hA, hB, -, -⟩ := hP
  have hent : ∀ a b, (locH Z p).Zhat P.A.f P.B.f a b =
      (Z.M p).L.cj (frFac Z.δ p a) * (frFac Z.δ p b *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Zhat F.fl F'.fl a b)) := by
    intro a b
    rw [hA, hB]
    show LocFacts₂ Z.M p (frFac Z.δ p b • baseChange₂ D p (frame F' b)) (frFac Z.δ p a • baseChange₂ D p (frame F a)) = _
    rw [Formalism.L2.SG.Pf.LocFacts.localForm_smul_left₂, Formalism.L2.SG.Pf.LocFacts.localForm_smul_right, baseChangeAt_form Z.M p (Z.hcj p)]
    simp only [Formalism.MainNotions.S.Zhat, frame]
    ring
  show (locH Z p).Dl P.A.f P.B.f l = _
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
  split_ifs with hl
  · rw [RingHom.map_det]
    have hM : ((locH Z p).Zhat P.A.f P.B.f).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        Matrix.of fun i j => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * (frFac Z.δ p (Fin.castLE hl j) *
          (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE) i j) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, hent]
    have e1 := Matrix.det_mul_column (fun i : Fin l => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)))
      (Matrix.of fun i j => frFac Z.δ p (Fin.castLE hl j) *
          (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE) i j)
    have e2 := Matrix.det_mul_row (fun j : Fin l => frFac Z.δ p (Fin.castLE hl j))
      (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE)
    simp only [Matrix.of_apply] at e1
    rw [RingHom.mapMatrix_apply, hM, e1, e2, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    set g : ℕ → (D.s.atP p).Ep := fun k => if h : k < D.R.rS + 1 then
      (Z.M p).L.cj (frFac Z.δ p ⟨k, h⟩) * frFac Z.δ p ⟨k, h⟩ else 1 with hg
    have h1 : (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1)
        = ∏ k ∈ Finset.range (D.R.rS + 1), if k < l then g k else 1 := by
      rw [← Fin.prod_univ_eq_prod_range (fun k => if k < l then g k else 1)]
      refine Finset.prod_congr rfl fun a _ => ?_
      show _ = (if a.val < l then g a.val else 1)
      rw [hg]; dsimp only; rw [dite_eq_left a.isLt]
    have h2 : (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i))
        = ∏ k ∈ Finset.range l, g k := by
      rw [← Fin.prod_univ_eq_prod_range g]
      refine Finset.prod_congr rfl fun i _ => ?_
      have : i.val < D.R.rS + 1 := lt_of_lt_of_le i.isLt hl
      show _ = g i.val
      rw [hg]; dsimp only; rw [dite_eq_left this]; rfl
    rw [h1, h2, ← Finset.prod_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · simp

end GlobalTheory.LocMinor
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem latMap_Lc_iff : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X ↔ Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) := by
  intro D X n γ hγ
  have key : GlobalTheory.SgGlob.latMap γ (Lc X) =
      (Formalism.HermitianLatticesTheory.gmap n (VS D).L0).comap ((vecOf X).restrictScalars (𝓞 D.host.E)) := by
    ext c
    simp only [GlobalTheory.SgGlob.latMap, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, Submodule.mem_comap, Lc,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨c', hc', rfl⟩
      exact ⟨vecOf X c', hc', n_vecOf hγ c'⟩
    · rintro ⟨y, hy, hny⟩
      refine ⟨crdH X y, by rw [vecOf_crdH]; exact hy, ?_⟩
      rw [← hγ, hny, crdH_vecOf]
  have hsurj : Function.Surjective ((vecOf X).restrictScalars (𝓞 D.host.E)) := fun y =>
    ⟨crdH X y, vecOf_crdH X y⟩
  rw [key]
  exact (Submodule.comap_injective_of_surjective hsurj).eq_iff

end GlobalTheory.CovDomGrp
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_adelic_correction_level_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (Fr : AdFrame cm.sig J Λ (gp 0 * gp 1) k) (h0 : UPts cm.sig J (Ad F)), (∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) → ∃ h1 : UPts cm.sig J (Ad F), (∀ x, (h1⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.St.G.level_char_match | exact GlobalTheory.St.G.level_char_match | (intros; apply GlobalTheory.St.G.level_char_match <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem coordLat_isLat (D : D7) (X : HidaSetting D) :
    IsLat ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
  have hcomb : ∀ x : Fin _ → D.host.E,
      Fintype.linearCombination D.host.E X.bas x = X.bas.equivFun.symm x := by
    intro x
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
  have heq : (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) =
      (VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, hcomb, Submodule.mem_map,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    constructor
    · intro hx
      exact ⟨_, hx, X.bas.equivFun.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [heq]
  refine ⟨Module.Finite.iff_fg.2 ((VS D).standardTuple_isLattice.fg.map _), ?_⟩
  have : ((VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap : Set (Fin _ → D.host.E)) =
      X.bas.equivFun.toLinearMap '' ((VS D).L0 : Set (VS D).V) := rfl
  have hspan : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) = ⊤ := by
    let V := VS D
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    change W = ⊤
    by_contra h
    let e : V.V ≃ₗ⋆[D.host.E] V.V :=
      (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
    let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
        Module.finrank D.host.E V.V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
      rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
        Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hzy : V.hT (e z) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hz)
      have hyz : V.hT y (e z) = 0 := by
        have hh := V.herm.eq (e z) y
        simpa [hzy] using hh.symm
      simp [hyz]
    let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
    let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.St.G
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem lintegral_comp_scale {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, 0 < s a)
    (G : (Fin r → ℂ) × ℂ → ENNReal) :
    ∫⁻ p : (Fin r → ℂ) × ℂ, G (fun a => (s a : ℂ) * p.1 a, p.2) =
      ENNReal.ofReal (∏ a, (s a ^ 2)⁻¹) * ∫⁻ p, G p := by
  let f : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
    LinearMap.pi fun i => ((s i • LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)
  let T : ((Fin r → ℂ) × ℂ) →ₗ[ℝ] ((Fin r → ℂ) × ℂ) := f.prodMap LinearMap.id
  have hdet : LinearMap.det T = ∏ a, s a ^ 2 := by
    simp only [T, f, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id,
      Complex.finrank_real_complex, mul_one]
  have hpos : 0 < ∏ a, s a ^ 2 := Finset.prod_pos fun a _ => pow_pos (hs a) 2
  have hne : LinearMap.det T ≠ 0 := hdet ▸ hpos.ne'
  haveI : (volume : Measure ((Fin r → ℂ) × ℂ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ((Fin r → ℂ) × ℂ)) hne
  let e : ((Fin r → ℂ) × ℂ) ≃ᵐ ((Fin r → ℂ) × ℂ) :=
    (T.equivOfDetNeZero hne).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : _ → _) = T := rfl
  have h := lintegral_map_equiv (μ := (volume : Measure ((Fin r → ℂ) × ℂ))) G e
  rw [he, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos), smul_eq_mul] at h
  rw [Finset.prod_inv_distrib, h]
  refine lintegral_congr fun p => ?_
  congr 1

theorem bcWeight_scale (k r : ℕ) (T T' : ℝ) (s : Fin r → ℝ) (hs : ∀ a, 0 < s a) (p : (Fin r → ℂ) × ℂ) :
    bcWeight k r T T' p = (∏ a, (s a ^ (2 * (Mdim k r a - 2)))⁻¹) *
      bcWeight k r T T' (fun a => (s a : ℂ) * p.1 a, p.2) := by
  unfold bcWeight
  split_ifs with h
  · rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    have := (hs a).ne'
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs a), mul_pow]
    field_simp
  · simp

theorem gamLev_inv_eq (k r : ℕ) (t : ℝ) (ht : 0 < t) :
    (D.GamLev k r t⁻¹ 1 0)⁻¹ = (∏ a : Fin r, ((t ^ (2 * (r - a.val))) ^ (2 * (Mdim k r a - 2)))⁻¹) *
      ∏ a : Fin r, ((t ^ (2 * (r - a.val))) ^ 2)⁻¹ := by
  unfold D.GamLev
  rw [Finset.prod_Ioc_succ_top (Nat.zero_le r), ← Finset.prod_mul_distrib]
  have h1 : Finset.Ioc 0 r = Finset.Ico 1 (r + 1) := by ext; simp; omega
  rw [h1, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_range]
  have h0 : ((r : ℤ) + 1 - ((r + 1 : ℕ) : ℤ)) = 0 := by push_cast; ring
  rw [h0]
  simp only [mul_zero, zero_mul, neg_zero, zpow_zero, div_one, mul_one]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  obtain ⟨d, hd⟩ : ∃ d, r = a.val + (d + 1) := ⟨r - a.val - 1, by have := a.isLt; omega⟩
  have h2 : r - a.val = d + 1 := by omega
  have h3 : Mdim k r a - 2 = 2 * d + k + 1 := by unfold Mdim; omega
  have h4 : 4 * ((r : ℤ) + 1 - ((1 + a.val : ℕ) : ℤ)) * (C.Mlev k r (1 + a.val) - 1) =
      ((2 * (d + 1) * (2 * (2 * d + k + 1)) + 2 * (d + 1) * 2 : ℕ) : ℤ) := by
    unfold C.Mlev
    have : (r : ℤ) = a.val + (d + 1) := by exact_mod_cast hd
    push_cast
    rw [this]; ring
  rw [h4, h2, h3, _root_.inv_zpow', neg_neg, zpow_natCast, ← pow_mul, ← pow_mul, pow_add, mul_inv]

theorem energy_change_of_frame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∫⁻ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p * Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) = ENNReal.ofReal (lamN L cN ^ 4 / D.GamLev k r ‖cStd / L.c‖⁻¹ 1 0) * B.normSq Bs (conjF (cStd / L.c) F) := by
  intro k r L μsec Bs cN F _ hstd hrat hc h0 htop
  have hJ := GlobalTheory.T.besselFunction_eq_scalar_sq_normalisedBessel_torusConjugate k r L μsec Bs cN F hstd hrat hc h0 htop
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  set α := cStd / L.c with hαdef
  have hB := (GlobalTheory.T.besselTorusElement_properties k r α hα).2.2.2
  have ht : 0 < ‖α‖ := norm_pos_iff.2 hα
  obtain ⟨hz, hz', -, -, -, -, -, hμ⟩ := hstd
  let s : Fin r → ℝ := fun a => ‖α‖ ^ (2 * (r - a.val))
  have hs : ∀ a, 0 < s a := fun a => pow_pos ht _
  let G : (Fin r → ℂ) × ℂ → ENNReal := fun p =>
    ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      ‖B.hsVec (B.JF Bs (conjF α F) (B.gq Bs p))‖ ^ 2)
  have hG : B.normSq Bs (conjF α F) = ∫⁻ p, G p := by
    simp only [B.normSq, jNormSq, hz, hz', G]
  let A : ℝ := lamN L cN ^ 4 * ∏ a, (s a ^ (2 * (Mdim k r a - 2)))⁻¹
  have hA : 0 ≤ A := mul_nonneg (by positivity)
    (Finset.prod_nonneg fun a _ => inv_nonneg.2 (pow_pos (hs a) _).le)
  have hhs : ∀ X : L.Wq →L[ℂ] L.Wp, Formalism.MainNotions.S.hsNormSq X = ‖B.hsVec X‖ ^ 2 := by
    intro X
    rw [PiLp.norm_sq_eq_of_L2]
    unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpt : ∀ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) =
      ENNReal.ofReal A * G (fun a => (s a : ℂ) * p.1 a, p.2) := by
    intro p
    simp only [G]
    rw [← ENNReal.ofReal_mul hA, hJ, hB, hhs, bcWeight_scale k r _ _ s hs p]
    congr 1
    have hsm : ∀ (c : ℂ) (X : L.Wq →L[ℂ] L.Wp), B.hsVec (c • X) = c • B.hsVec X := fun _ _ => rfl
    rw [hsm, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [B.gq, hμ, A, s]
    ring
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_scale s hs G,
    hG, ← mul_assoc, ← ENNReal.ofReal_mul hA, div_eq_mul_inv, gamLev_inv_eq k r _ ht]
  simp only [A, s, mul_assoc]

end GlobalTheory.ThA
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.flagClass_measure_bound_lattice_stabiliser : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (p q : ℕ), HasSig I p q → ∀ (c : InfinitePlace I.F → ℝ) (c₀ : InfinitePlace I₀.F → ℝ), IsGaugeAll I c → IsGaugeAll I₀ c₀ → ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a → ENNReal.ofReal (∏ v, c v) * covol (flagGroup I xf S) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) {g | sizesAt I xf S g ∈ B} ≤ ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) * (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) * (ENNReal.ofReal (∏ v, c₀ v) * covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ) * ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) := by
  first | exact @GlobalTheory.FlagBase.OneClass.bound | exact GlobalTheory.FlagBase.OneClass.bound | (intros; apply GlobalTheory.FlagBase.OneClass.bound <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.covolume_integralUnipotentStabilizer_of_term : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → ∀ (p : Point D.host.E (D.R.rS + 1)) (L U : GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D F0) F') = L * ptMat p * U → ∃ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) ≤ ENNReal.ofReal (HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ^ (C * (D.R.rS : ℝ) ^ 2)) ∧ ∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ, ∃ n ∈ NLam Λ (lf D F0) ∩ NLam Λ F', ∃ a : GramM D, (∀ j : Fin (D.R.rS + 1), n (frame F' j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame F' i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat p)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω := by
  first | exact @GlobalTheory.LoopC.CovTerm.covolume_term | exact GlobalTheory.LoopC.CovTerm.covolume_term | (intros; apply GlobalTheory.LoopC.CovTerm.covolume_term <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_exactGram_frame_in_termClass : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (Z : GramM D), ∀ F' ∈ FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P, ∃ F'' ∈ ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P, TEqv D Λ (lf D F0) F' F'' := by
  first | exact @GlobalTheory.LoopC.FrameMove.exists_exact_frame | exact GlobalTheory.LoopC.FrameMove.exists_exact_frame | (intros; apply GlobalTheory.LoopC.FrameMove.exists_exact_frame <;> assumption)
end
