module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle080
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle083
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalDenominators
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle082
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle067
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle037
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
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ}

theorem q_ne (g : Formalism.MainNotions.S.Loc.SplitG M.L) : ((g.q : F)) ≠ 0 := by
  exact fun h => g.q_irr.ne_zero (Subtype.ext h)

theorem zzrel_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    X'.map (π1 M g) = L.map (π1 M g) * X.map (π1 M g) * P.map (π1 M g) ∧
    (X'.map (π2 M g))ᵀ = L.map (π2 M g) * (X.map (π2 M g))ᵀ * P.map (π2 M g) := by
  classical
  have hq : (g.q : F) ≠ 0 := q_ne M g
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hZ : ∀ (Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)),
      Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T' a b =
        g.e.symm ((g.e (Y a b)).1 / (g.q : F), -((g.e (Y b a)).2 / (g.q : F))) -
        (if a = Fin.last r ∧ b = Fin.last r then g.e.symm (-T / (g.q : F), T' / (g.q : F)) else 0) := by
    intro Y a b
    simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, Matrix.of_apply]
  let Ec : Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
    Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0
  have hZ1 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π1 M g) =
      (g.q : F)⁻¹ • Y.map (π1 M g) + (T / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.fst_zero, sub_zero, Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul,
        mul_zero, add_zero]
      ring
  have hZ2 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π2 M g) =
      -((g.q : F)⁻¹ • (Y.map (π2 M g))ᵀ) - (T' / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, Ec, Matrix.of_apply,
        smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.snd_zero, sub_zero, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.transpose_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_zero]
      ring
  have hE : ∀ φ : E →+* F, L.map φ * Ec * P.map φ = Ec := by
    intro φ
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Ec, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · simp only [and_self, if_true, mul_one, hL, hP]
        split_ifs <;> simp_all
      · intro k _ hk
        simp [hk]
      · simp
    · intro l _ hl
      simp [hl]
    · simp
  have hinv : (g.q : F)⁻¹ ≠ 0 := inv_ne_zero hq
  constructor
  · have hmap := congrArg (fun Z => Matrix.map Z (π1 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ1, hZ1] at hmap
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hE] at hmap
    exact smul_right_injective _ hinv (add_right_cancel hmap)
  · have hmap := congrArg (fun Z => Matrix.map Z (π2 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ2, hZ2] at hmap
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      hE] at hmap
    exact smul_right_injective _ hinv (neg_inj.1 (sub_left_inj.1 hmap))

theorem condX_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * X * uuG M g L P = X' := by
  obtain ⟨h1, h2⟩ := zzrel_G M g hs hL hP T T' h
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hcj : ∀ x : E, g.e ((M.L.cj : E →+* E) x) = (g.e x).swap := fun x => g.e_cj x
  ext i j
  apply g.e.injective
  refine Prod.ext ?_ ?_
  · have h1' := congrArg (fun A => A i j) h1
    simp only [Matrix.map_apply, Matrix.mul_apply, hπ1, Finset.sum_mul] at h1'

    simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.fst_sum,
    Prod.fst_mul, hcj, Prod.fst_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h1']
  · have h2' := congrArg (fun A => A j i) h2
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, hπ2, Finset.sum_mul] at h2'

    simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.snd_sum,
    Prod.snd_mul, hcj, Prod.snd_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h2', Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

theorem condM_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * cornerM c * mmG M g L P = cornerM c := by
  have hm : ∀ i, mmG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [mmG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem condU_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (uuG M g L P) * cornerM c * uuG M g L P = cornerM c := by
  have hm : ∀ i, uuG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [uuG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohIntPf

variable {D : Formalism.BasicNotions.D7}

theorem exists_den {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsBaseFieldIntegerDenominator.exists_den hΛ x

variable (Zd : LocDat D)

theorem bcP_mem_cof {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    {p : PlF D | baseChange₂ D p x ∉ lattice₂ D Zd.M p Λ}.Finite := by
  obtain ⟨d, hd, hdx⟩ := exists_den hΛ x
  have hI : Ideal.span {d} ≠ (0 : Ideal (𝓞 D.host.F)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  refine (Ideal.finite_factors hI).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hnd
  apply hp
  have := p.isPrime
  letI := hΛ
  rw [Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ) (by infer_instance)]
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).2 ⟨d, hnd, hdx⟩

theorem scal_mem {p : PlF D} (hs : (Zd.M p).split = none)
    (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (b : Fin (D.R.rS + 1)) : TermLoc.sgnP' D p b * frFac Zd.δ p b ∈ (D.s.atP p).O := by
  have hs' : (D.s.atP p).split = none := by
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hs] at hA
    cases h2 : (D.s.atP p).split with
    | none => rfl
    | some sg =>
      rw [h2] at hA
      exact (hA : False).elim
  refine Subring.mul_mem _ ?_ ?_
  · unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
  · rw [Formalism.L2.SG.Pf.BBTie.bt_frFac_eq Zd p b]
    set w : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ *
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw
    have hwO : w ∈ (D.s.atP p).O :=
      Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ.2) hu.2
    have hinv : (((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = w := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec]
      show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) * w = 1
      rw [hw]
      have hδ0 : Zd.δ p ≠ 0 := (Zd.agree p).2.1
      have hu0 := Formalism.L2.SG.Pf.BBTie.uP_ne (D := D) p
      calc algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹))
          = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p * (Zd.δ p)⁻¹) *
            (D.s.atP p).ιE ((uP p : D.host.E) * (uP p : D.host.E)⁻¹) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [mul_inv_cancel₀ hδ0, mul_inv_cancel₀ hu0, map_one, map_one, mul_one]
    rw [Units.val_pow_eq_pow_val, hinv]
    exact Subring.pow_mem _ hwO _

end CohIntPf

open CohIntPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem cohInt_holds : CohInt Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' _
  have hΛ : Submodule.IsFullLattice D.host.E γ.lam := (hP.2.1.1 γ.lam γ.mem).1.1
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅
  rw [Filter.eventually_cofinite] at hgood
  refine (hgood.union (Set.finite_iUnion fun b => bcP_mem_cof Zd hΛ (frame F'₂ b))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hn
  obtain ⟨hg, hb⟩ := hn
  apply hp
  intro b
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (scal_mem Zd hg.1 hg.2.1 hg.2.2.1 b) (hb b)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem XP_eq_ZZP {p : PlF D} (hA : Agree δ M p) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) (heq : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U) :
    XP M δ u u' (p := p) w L U = Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') := by
  unfold XP Y0
  rw [← move δ M u u' hA L U hL hU, Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM, ← heq,
    Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM]

theorem int_zzp (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    ∀ i j, (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) i j ∈
      (M p).R := by
  obtain ⟨hAg, hT, hrows, -, hel, ⟨hPD, hmk⟩, hadm, -⟩ := hE
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := Formalism.L2.SG.TermDef.Gt_mk hTF.1 ⟨F', hPD⟩
  have hGen := Formalism.L2.SG.TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨F', hPD⟩
  rw [hmk] at hGt hGen
  have hEZ : F' ∈ Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') F0 γ.lam (ZhatL (lf D F0) F') :=
    ⟨⟨hPD.1, hPD.2.1, fun h => hel.1.2 (hGt.trans h)⟩, hadm, hGen.1 hel.1.1, hPD.2.2, rfl⟩
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hAg u u' hT F0 what₂ hrows γ.lam γ.mem (ZhatL (lf D F0) F') F' hEZ p
  intro i j
  simp only [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI i j) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.CountAt
end
end

section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem qbar_qbar (q : FreeE w) : qbar w (qbar w q) = q := by
  apply Subtype.ext
  simp only [qbar, pinv_pinv]

theorem hgt_qbar (q : FreeE w) : hgt w (qbar w q) = hgt w q := by
  unfold hgt qbar
  have h1 := pinv_add w q.1.1 q.1.2 q.2.2
  have h2 : q.1.1.val < q.1.2.val := q.2.1
  simp only
  omega

theorem sgm_pinv_eq (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    sgm (pinv w c) (pinv w a) = (sgm a c : D.host.E) := by
  have h := sgm_pinv w a c hs
  rcases sgm_cases a c with e | e
  · rw [e, one_mul] at h; rw [h, e]
  · rw [e] at h ⊢; linear_combination -h

theorem sgq_qbar (q : FreeE w) : sgq w (qbar w q) = sgq w q :=
  sgm_pinv_eq w q.1.1 q.1.2 q.2.2

theorem Xinv_q (y : FreeE w → D.host.E) (q : FreeE w) :
    (Xmat w y)⁻¹ q.1.1 q.1.2 = cf w y q - y q := by
  have h := inv_diff (Xmat_upU w y) (Xmat_upU w (trunc w y (hgt w q))) q.2.1 (fun i j hij hh => by
    by_cases hb : i < j ∧ blkOf w.1 i.val = blkOf w.1 j.val
    · simp only [Xmat, ne_of_lt hij, if_false, dif_pos hb, trunc]
      rw [if_pos (show hgt w ⟨(i, j), hb⟩ < hgt w q from hh)]
    · simp only [Xmat, ne_of_lt hij, if_false, dif_neg hb])
  rw [Xmat_q, Xmat_q] at h
  have h0 : trunc w y (hgt w q) q = 0 := by unfold trunc; rw [if_neg (lt_irrefl _)]
  rw [h0] at h
  unfold cf
  linear_combination h

theorem cf_mem (y : FreeE w → D.host.E) (q : FreeE w)
    (hy : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p)) : cf w y q ∈ ddPow D (hgt w q) := by
  unfold cf
  refine grD_inv (Xmat_upU w _) (Xmat_grD w _ fun p => ?_) q.1.1 q.1.2 (le_of_lt q.2.1)
  unfold trunc
  split_ifs with h
  · exact hy p h
  · exact FractionalIdeal.zero_mem _

theorem E_q (y : FreeE w → D.host.E) (q : FreeE w) :
    (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 =
      y q - sgq w q * D.conjF (cf w y (qbar w q) - y (qbar w q)) := by
  rw [Matrix.sub_apply, Xmat_q]
  have h := Xinv_q w y (qbar w q)
  simp only [Psi]
  rw [show (Xmat w y)⁻¹ (pinv w q.1.2) (pinv w q.1.1) = cf w y (qbar w q) - y (qbar w q) from h]
  rfl

theorem condX_third (X : MatR D) (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    X (pinv w c) (pinv w a) - D.conjF (bt D X⁻¹ a c) = (X - Psi w X⁻¹) (pinv w c) (pinv w a) := by
  rw [Matrix.sub_apply]
  simp only [Psi, pinv_pinv]
  rw [sgm_pinv_eq w a c hs]
  simp only [bt, sgm, map_mul, map_pow, map_neg, map_one]
  ring

theorem bt_mem {X : MatR D} (hG : GrD X) (a c : Fin (D.R.rS + 1)) (hac : a < c) :
    bt D X a c ∈ ddPow D (c.val - a.val) := by
  have h := hG a c (le_of_lt hac)
  rw [show bt D X a c = sgm a c * X a c by simp only [bt, sgm]; ring]
  rcases sgm_cases a c with e | e
  · rw [e, one_mul]; exact h
  · rw [e, neg_one_mul]; exact (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem h

theorem condX_iff (y : FreeE w → D.host.E) :
    CondX w (Xmat w y) ↔ (∀ q, y q ∈ ddPow D (hgt w q)) ∧
      ∀ q, (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) := by
  constructor
  · intro h
    have hy : ∀ q, y q ∈ ddPow D (hgt w q) := by
      intro q
      obtain ⟨h1, -, -⟩ := h (qbar w q).1.1 (qbar w q).1.2 (qbar w q).2.1 (qbar w q).2.2
      have e := hgt_qbar w q
      unfold hgt at e
      simp only [qbar, pinv_pinv] at h1 e
      rw [e, Xmat_q] at h1
      exact h1
    refine ⟨hy, fun q => ?_⟩
    obtain ⟨-, -, h3⟩ := h (qbar w q).1.1 (qbar w q).1.2 (qbar w q).2.1 (qbar w q).2.2
    rw [condX_third w _ _ _ (qbar w q).2.2] at h3
    have e := hgt_qbar w q
    unfold hgt at e
    simp only [qbar, pinv_pinv] at h3 e
    rw [e] at h3
    exact h3
  · rintro ⟨hy, hE⟩ a c hac hs
    have hG := grD_inv (Xmat_upU w y) (Xmat_grD w y hy)
    set p : FreeE w := qbar w ⟨(a, c), hac, hs⟩ with hp
    have hpe : hgt w p = c.val - a.val := hgt_qbar w _
    have hp1 : Xmat w y (pinv w c) (pinv w a) = y p := Xmat_q w y p
    refine ⟨?_, bt_mem hG a c hac, ?_⟩
    · rw [hp1, ← hpe]; exact hy p
    · rw [condX_third w _ a c hs, ← hpe]; exact hE p

end Formalism.L2.SG.Pf.StabIntLat
end
end
