module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle809
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

noncomputable def atW (w : Pl D.host.E) : AE D →+* Kw w := (cpt w).comp (toEAf D)

theorem atW_apply (w : Pl D.host.E) (a : AE D) : atW w a = cpt w (toEAf D a) := rfl

theorem atW_atPl_self (w : Pl D.host.E) (x : Kw w) : atW w (atPl w x) = x := by
  classical
  rw [atW_apply, (atPl_spec w x).2 w, Pi.single_eq_same]

theorem atW_atPl_ne {w w' : Pl D.host.E} (h : w ≠ w') (x : Kw w') : atW w (atPl w' x) = 0 := by
  classical
  rw [atW_apply, (atPl_spec w' x).2 w, Pi.single_eq_of_ne h]

theorem atPl_one_mul (w : Pl D.host.E) (z : Kw w) : atPl w 1 * atPl w z = atPl w z := by
  classical
  refine ae_ext (by rw [map_mul, (atPl_spec w 1).1, zero_mul, (atPl_spec w z).1]) fun Q => ?_
  rw [map_mul, map_mul, (atPl_spec w 1).2 Q, (atPl_spec w z).2 Q]
  by_cases h : Q = w
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_mul]

namespace CoordinateMaps

variable (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
  (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)

theorem coord_add (y y' : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (y + y') = B.coord t w hX hY y + B.coord t w hX hY y' := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

theorem coord_zero : B.coord t w hX hY 0 = 0 := by
  unfold Frames.coord
  rw [Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem coord_surj (z : Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w)) :
    ∃ y, B.coord t w hX hY y = z := by
  refine ⟨(loc w (B.β X.1 X.2)).val * (zᵀ.submatrix (Fin.cast (rank_vertex G t w hX).symm)
    (Fin.cast (rank_vertex G t w hY).symm)) * ((loc w (B.β Y.1 Y.2))⁻¹).val, ?_⟩
  unfold Frames.coord
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  ext a b
  simp only [transpose_apply, submatrix_apply, Fin.cast_cast, Fin.cast_eq_self]

end CoordinateMaps

end GlobalTheory.BigDat

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem map_atW_smul (w : Pl D.host.E) {m n : Type} (M : Matrix m n (AE D)) :
    (atPl w 1 • M).map (atW w) = M.map (atW w) := by
  refine Matrix.ext fun a b => ?_
  rw [map_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, atW_atPl_self, one_mul]

theorem mixCo_eq (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) (u : Pt G i j) :
    mixCo B t e w u = fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mapV e u).map (atW w)))
      (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((mapW e u).map (atW w)))ᵀ := rfl

theorem mixCo_spec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E),
    (∀ u x : Pt G i j, mixCo B t e w (u + x) = mixCo B t e w u + mixCo B t e w x) ∧
    (∀ z, ∃ x ∈ mixHalf e (atPl w 1), mixCo B t e w x = z) ∧
    (∀ u : Pt G i j, mixCo B t e w (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = mixCo B t e w u) ∧
    ∀ w' : Pl D.host.E, w' ≠ w → ∀ x ∈ mixHalf e (atPl w' 1), mixCo B t e w x = 0 := by
  intro D T L sc G B t i j e w
  refine ⟨fun u x => ?_, fun z => ?_, fun u => ?_, fun w' hw x hx => ?_⟩
  · rw [mixCo_eq, mixCo_eq, mixCo_eq, mapV_add, mapW_add, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
      CoordinateMaps.coord_add, CoordinateMaps.coord_add, transpose_add]
    exact Matrix.ext fun a b => by rcases b with b | b <;> rfl
  · obtain ⟨y₁, hy₁⟩ := CoordinateMaps.coord_surj B t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      z.toCols₁
    obtain ⟨y₂, hy₂⟩ := CoordinateMaps.coord_surj B t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
      z.toCols₂ᵀ
    let x₁ : HomV G i j := y₁.map (atPl w)
    let x₂ : HomW G i j := y₂.map (atPl w)
    have k₁ : mapV e (ofMaps e (x₁, x₂)) = x₁ := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (x₁, x₂)) = x₂ := mapW_ofMaps e _
    have m₁ : x₁.map (atW w) = y₁ := Matrix.ext fun a b => atW_atPl_self w _
    have m₂ : x₂.map (atW w) = y₂ := Matrix.ext fun a b => atW_atPl_self w _
    refine ⟨ofMaps e (x₁, x₂), ⟨?_, ?_⟩, ?_⟩
    · show IsHalf _ (mapV e _)
      rw [k₁]
      intro a b
      exact atPl_one_mul w _
    · show IsHalf _ (mapW e _)
      rw [k₂]
      intro a b
      exact atPl_one_mul w _
    · rw [mixCo_eq, k₁, k₂, m₁, m₂, hy₁, hy₂, transpose_transpose, fromCols_toCols]
  · have k₁ : mapV e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapV e u := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapW e u := mapW_ofMaps e _
    rw [mixCo_eq, mixCo_eq, k₁, k₂, map_atW_smul, map_atW_smul]
  · have h₁ : (mapV e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapV e x a b) = atW w (atPl w' 1 * mapV e x a b) := congrArg _ (hx.1 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    have h₂ : (mapW e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapW e x a b) = atW w (atPl w' 1 * mapW e x a b) := congrArg _ (hx.2 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    rw [mixCo_eq, h₁, h₂, CoordinateMaps.coord_zero, CoordinateMaps.coord_zero, transpose_zero, fromCols_zero]

end GlobalTheory.BigDat

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] {v : Pl D.host.F} {z : M}
    (h : At (evFin D.host.F v) z) : liftV v (1 : Fv D.host.F v) • z = z := by
  have h1 := h (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm

theorem at_smul {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] (v : Pl D.host.F) (z : M) :
    At (evFin D.host.F v) (liftV v (1 : Fv D.host.F v) • z) := fun u hu => by
  rw [smul_smul, ← smul_eq_mul u, at_liftV v 1 u hu, zero_smul]

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z :=
  map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c z

theorem symplO_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : symplO S T x (c • y) = symplO S T (c • x) y := by
  have h : hO S T x (c • y) = hO S T (c • x) y := by
    unfold hO
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  unfold symplO
  rw [h]

theorem infPart_smul (v : Pl D.host.F) (z : AE D) : infPart D (liftV v (1 : Fv D.host.F v) • z) = 0 := by
  rw [Algebra.smul_def, RingHom.map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (liftV v (1 : Fv D.host.F v))) = 0 := infPart_pair _ _
  rw [this, zero_mul]

theorem smul_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (v : Pl D.host.F)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h : liftV v (1 : Fv D.host.F v) • finTens α M = finTens (singleFin v 1 * α) M := by
      ext i j
      change (pairA D.host.F 0 (singleFin v 1) * pairA D.host.F 0 α) ⊗ₜ[D.host.F] M i j = _
      rw [pair_mul]
      rfl
    rw [h]
    refine finTens_mem_latO (mul_mem_intAf (fun w => ?_) hα) hM
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleFin_self]
      exact one_mem _
    · rw [evalV_singleFin_ne hw]
      exact zero_mem _
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem isHalf_smul {m n : ℕ} {ε : AE D} (c : AF D.host.F) {u : Mx D m n} (hu : IsHalf ε u) : IsHalf ε (c • u) :=
  fun i j => by rw [Matrix.smul_apply, mul_smul_comm, hu]

theorem isHalf_zero {m n : ℕ} (ε : AE D) : IsHalf ε (0 : Mx D m n) := fun _ _ => mul_zero _

section Pair

variable {S T S' T' : HSp D} {P : Type} [AddCommGroup P] [Module (AF D.host.F) P]
  (m : P ≃ₗ[AF D.host.F] WO S T × WO S' T') (v : Pl D.host.F) (Λ : AddSubgroup P)

theorem le_of_gen {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)}
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T LS LT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' LS' LT' fun _ => True) (H : AddSubgroup P) (h2 : ∀ u ∈ Λ, 2 • u ∈ H)
    (hh : ∀ ε, IsSplitIdem D ε → ∀ u ∈ Λ, IsHalf ε (m u).1 → IsHalf ε (m u).2 → u ∈ H) : Λ ≤ H := by
  let f : WO S T × WO S' T' →ₗ[AF D.host.F] P := liftV v (1 : Fv D.host.F v) • m.symm.toLinearMap
  have hf : ∀ x, f x = liftV v (1 : Fv D.host.F v) • m.symm x := fun _ => rfl
  have hm : ∀ x, m (f x) = liftV v (1 : Fv D.host.F v) • x := fun x => by rw [hf, map_smul, m.apply_symm_apply]
  have hin : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T LS LT (fun _ => True) →
      x.2 ∈ latO S' T' LS' LT' (fun _ => True) → f x ∈ Λ := fun x h1 h2 =>
    (hΛ _).2 ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩
  intro u hu
  obtain ⟨ha, h1, h1'⟩ := (hΛ u).1 hu
  have e : u = f ((m u).1, 0) + f (0, (m u).2) := by
    rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, hf, Prod.mk.eta, m.symm_apply_apply, smul_eq_of_at ha]
  rw [e]
  refine add_mem ?_ ?_
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inl _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (x, 0) hx (zero_mem _))
    · exact hh ε hε (f (x, 0)) (hin (x, 0) hx (zero_mem _)) (by rw [hm]; exact isHalf_smul _ hx')
        (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inr _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1'
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (0, x) (zero_mem _) hx)
    · exact hh ε hε (f (0, x)) (hin (0, x) (zero_mem _) hx) (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
        (by rw [hm]; exact isHalf_smul _ hx')

theorem mem_iff_char {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T ΛS ΛT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' ΛS' ΛT' fun _ => True) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (B : P → P → AF D.host.F) (hB : ∀ x y, B x y = symplO S T (m x).1 (m y).1 + symplO S' T' (m x).2 (m y).2)
    {z : P} (hz : At (evFin D.host.F v) z) : z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1 := by
  constructor
  · intro h γ hγ
    obtain ⟨-, a, b⟩ := (hΛ z).1 h
    obtain ⟨-, a', b'⟩ := (hΛ γ).1 hγ
    rw [hB, AddChar.map_add_eq_mul, char_sympl_eq_one hψ hS hT a a', char_sympl_eq_one hψ hS' hT' b b', one_mul]
  · intro h
    have hm : ∀ x, m (liftV v (1 : Fv D.host.F v) • m.symm x) = liftV v (1 : Fv D.host.F v) • x := fun x => by
      rw [map_smul, m.apply_symm_apply]
    have hz' : liftV v (1 : Fv D.host.F v) • m z = m z := by rw [← map_smul, smul_eq_of_at hz]
    have hz1 : liftV v (1 : Fv D.host.F v) • (m z).1 = (m z).1 := congrArg Prod.fst hz'
    have hz2 : liftV v (1 : Fv D.host.F v) • (m z).2 = (m z).2 := congrArg Prod.snd hz'
    have key : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T ΛS ΛT (fun _ => True) →
        x.2 ∈ latO S' T' ΛS' ΛT' (fun _ => True) → ψ (symplO S T (m z).1 x.1 + symplO S' T' (m z).2 x.2) = 1 := fun x h1 h2 => by
      have := h _ ((hΛ (liftV v (1 : Fv D.host.F v) • m.symm x)).2
        ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩)
      rwa [hB, hm, Prod.smul_fst, Prod.smul_snd, symplO_swap, symplO_swap, hz1, hz2] at this
    refine (hΛ z).2 ⟨hz, mem_of_char hψ hS hT ?_ fun x hx => ?_, mem_of_char hψ hS' hT' ?_ fun x hx => ?_⟩
    · rw [← hz1]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S' T' (m z).2 0 = 0 := (symplHom S' T' (m z).2).map_zero
      have := key (x, 0) hx (zero_mem _)
      rwa [h0, add_zero] at this
    · rw [← hz2]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S T (m z).1 0 = 0 := (symplHom S T (m z).1).map_zero
      have := key (0, x) (zero_mem _) hx
      rwa [h0, zero_add] at this

end Pair

theorem latPt_le_closure_and_selfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ v : Pl D.host.F, latPt e v ≤ AddSubgroup.closure (genPt e v) ∧
      ∀ z : Pt G i j, At (evFin D.host.F v) z → (z ∈ latPt e v ↔ ∀ γ ∈ latPt e v, W.ψ (sympPt Γ z γ) = 1) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v
  have a := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨le_of_gen (maps e) v _ (fun _ => Iff.rfl) _ (fun u hu => AddSubgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩))
    fun ε hε u hu h1 h2 => AddSubgroup.subset_closure (Or.inr ⟨hu, ε, hε, h1, h2⟩), fun z hz => ?_⟩
  exact mem_iff_char (maps e) v _ (isSelfDualC_neg a) (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd a (fun _ => Iff.rfl) W.ψ_std (sympPt Γ) (symp_eq e Γ hW hWW) hz

end GlobalTheory.BigDatLat

end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem substF_minorPol_eq_sum : ∀ (D : D7) {a d : ℕ} {m : D.what₂.Tau → ℕ} (K : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ)
    (T : Tup D a d m), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (minorPol D T) =
      ∑ T' : Tup D a d m, (∏ τ, ∏ r, (Matrix.of fun i i' : Fin a => K τ ((T' τ r).1 i') ((T τ r).1 i)).det) •
        minorPol D T' := by
  intro D a d m K T
  have hmin : ∀ τ (s : Fin a → Fin d), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))
      (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det =
      ∑ s' : {s : Fin a → Fin d // StrictMono s},
        MvPolynomial.C ((Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)).det) *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s'.1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det]
    have hM : (GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))).mapMatrix
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
        (Matrix.of fun (i : Fin a) (k : Fin d) => (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) *
        (Matrix.of fun (k : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, k, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) := by
      refine Matrix.ext fun i i' => ?_
      simp only [RingHom.mapMatrix_apply, AlgHom.coe_toRingHom, Matrix.map_apply, Matrix.of_apply,
        GlobalTheory.CompactHowe.substF_X, Matrix.mul_apply, Matrix.one_apply]
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single i']
      · simp
      · intro l _ hl; simp [Matrix.one_apply_ne hl]
      · simp
    rw [hM, GlobalTheory.MinorFrame.det_mul_eq_sum_sm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    congr 1
    rw [show (Matrix.of fun (i : Fin a) (k : Fin d) =>
        (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).submatrix id s'.1 =
        (MvPolynomial.C : ℂ →+* MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ).mapMatrix
          (Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)) from by ext; simp]
    rw [← RingHom.map_det]
  unfold minorPol
  simp only [map_prod, hmin]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T' _ => ?_
  rw [← MvPolynomial.C_mul']
  simp only [Finset.prod_mul_distrib, map_prod]

end GlobalTheory.NormDict
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj : ∀ {D : D7} {S S' : HSp D} (I : GlobalTheory.Mem.Isom.IsoMat S S') (m : MeasureTheory.Measure (GA D S)) (fd : Set (GA D S)),
  m.IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ S) fd m →
  (m.map I.kap).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ S') (I.kap.symm ⁻¹' fd) (m.map I.kap) := by
  intro D S S' I m fd ⟨h1, h2⟩
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GA D S') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (GA D S') := ⟨rfl⟩
  refine ⟨I.kap.isHaarMeasure_map m I.continuous_kap I.continuous_kap_symm, ?_⟩
  have hm : Measurable I.kap := I.continuous_kap.measurable
  have hm' : Measurable I.kap.symm := I.continuous_kap_symm.measurable
  have hq : MeasureTheory.Measure.QuasiMeasurePreserving I.kap.symm (m.map I.kap) m := by
    refine ⟨hm'.aemeasurable, ?_⟩
    rw [MeasureTheory.Measure.map_map hm' hm]
    have : (I.kap.symm : GA D S' → GA D S) ∘ I.kap = id := funext fun x => I.kap.symm_apply_apply x
    rw [this, MeasureTheory.Measure.map_id]
  let e : GQ S ≃ GQ S' :=
    { toFun := fun γ => ⟨I.kap γ, I.kap_mem_GQ γ.2⟩
      invFun := fun γ => ⟨I.kap.symm γ, I.symm.kap_mem_GQ γ.2⟩
      left_inv := fun γ => Subtype.ext (I.kap.symm_apply_apply _)
      right_inv := fun γ => Subtype.ext (I.kap.apply_symm_apply _) }
  refine h2.preimage_of_equiv hq (e := e) e.bijective fun γ x => ?_
  show I.kap.symm (I.kap γ * x) = (γ : GA D S) * I.kap.symm x
  rw [map_mul, MulEquiv.symm_apply_apply]
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.twice_picardClass_eq_zero_of_translates_mem_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), A.hom ⁻¹ᵁ U ≤ W → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A), (∀ y, Y.hom y ∈ U) → (∀ y, v.left y ∈ V) → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → ∀ l : Y.left ⟶ W.toScheme, l ≫ W.ι = x.left → GlobalTheory.CechPic.pull l (2 • c) = 0 := by
  first | exact @GlobalTheory.twice_cls_eq_zero_of_translates_mem | exact GlobalTheory.twice_cls_eq_zero_of_translates_mem | (intros; apply GlobalTheory.twice_cls_eq_zero_of_translates_mem <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ t : ℝ, 0 < t → ∀ lam : Fin a → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * ∏ i, r i ^ lam i := by
  first | exact @GlobalTheory.cuspForm_rapidDecay_siegel | exact GlobalTheory.cuspForm_rapidDecay_siegel | (intros; apply GlobalTheory.cuspForm_rapidDecay_siegel <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

theorem _root_.GlobalTheory.T.exists_secondKindCoordinates_unitaryArchimedeanPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (s : GArch σ J w → Fin d → ℝ), (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝 1) (𝓝 0) ∧ ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
  first | exact @GlobalTheory.UAut.exists_coordSecondKind_arch | exact GlobalTheory.UAut.exists_coordSecondKind_arch | (intros; apply GlobalTheory.UAut.exists_coordSecondKind_arch <;> assumption)
end
