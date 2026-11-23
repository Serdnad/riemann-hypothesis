module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle063
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle083
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupActB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle074
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle080
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfInputs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle069
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle076
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle085
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LastCoordMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountCos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle086
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle042
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMemAsp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle082
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolAsm

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolAct Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbitAction_holds : Formalism.L2.SG.Pf.ZsVolOrb.OrbActE M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  have hL : IsLoUni L := hH.2.2.2.2.2.2.2.1
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  set C := CZ M δ u u' (ZhatL (lf D F0) F') L with hC
  set S := (PairVal.stabAut D u u' F0 what₂ γ F' L).subgroupOf C with hS

  have hdat : ∀ g : C, ∃ (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V)
      (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)),
      ((g : GLR D) : MatR D) = L⁻¹ * (a' : MatR D) * L ∧ LiftData u u' F0 what₂ γ F' a' b ν m F₂ := by
    intro g
    have hg := (Formalism.L2.SG.Pf.ZsVolGrp.mem_CZ M δ u u' _ L hLd g).1 g.2
    obtain ⟨a', ha, hlo, b, hb, hZ, hsh⟩ := (Formalism.L2.SG.Pf.ZsVolShape.mem_stZSet_iff M δ u u' hH.1 _ L g).1 hg
    obtain ⟨ν, m, F₂, hd⟩ := Formalism.L2.SG.Pf.TupActB.moveCZ_holds M δ u u' F0 what₂ γ w F' L U hH a' b hlo hb hZ hsh
    exact ⟨a', b, ν, m, F₂, ha, hd⟩
  choose A Bm Nu Mu F2 hAL hD using hdat
  set Z := ZhatL (lf D F0) F' with hZdef
  let cls : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) → Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :=
    fun F => {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧ CntLocal.NilradicalFlagMoved F0 γ.lam F F''}
  have hmem : ∀ g : C, cls (F2 g) ∈ PairVal.orbT D u u' F0 what₂ γ Z := fun g =>
    ⟨F2 g, (hD g).2.2.2.2.2.2.2.2.1, (hD g).2.2.2.2.2.2.2.2.2.1, rfl⟩
  let ψ : C → PairVal.orbT D u u' F0 what₂ γ Z := fun g => ⟨cls (F2 g), hmem g⟩
  have hcls : ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E),
      F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z →
      (cls F₁ = cls F₂ ↔ CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂) := by
    intro F₁ F₂ h₂
    constructor
    · intro h
      have : F₂ ∈ cls F₂ := ⟨h₂, Formalism.L2.SG.Pf.TupOrb.n0rel_refl' γ.lam F₂⟩
      rw [← h] at this
      exact this.2
    · intro h
      ext F''
      constructor
      · rintro ⟨hE, h1⟩
        exact ⟨hE, Formalism.L2.SG.Pf.TupOrb.n0rel_trans (Formalism.L2.SG.Pf.TupOrb.n0rel_symm h) h1⟩
      · rintro ⟨hE, h2⟩
        exact ⟨hE, Formalism.L2.SG.Pf.TupOrb.n0rel_trans h h2⟩
  have hψ : ∀ g₁ g₂ : C, ψ g₁ = ψ g₂ ↔ g₁⁻¹ * g₂ ∈ S := by
    intro g₁ g₂
    rw [Subtype.ext_iff, hS, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show cls (F2 g₁) = cls (F2 g₂) ↔ _
    rw [hcls _ _ (hD g₂).2.2.2.2.2.2.2.2.1]
    exact fibreIndex_holds M δ u u' F0 what₂ γ w F' L U hH (A g₁) (Bm g₁) (Nu g₁) (Mu g₁) (F2 g₁) (A g₂) (Bm g₂)
      (Nu g₂) (Mu g₂) (F2 g₂) g₁ g₂ (hAL g₁) (hAL g₂) (hD g₁) (hD g₂)
  let φ : C ⧸ S → PairVal.orbT D u u' F0 what₂ γ Z :=
    Quotient.lift ψ (fun a b h => (hψ a b).2 (QuotientGroup.leftRel_apply.1 h))
  have hinj : Function.Injective φ := by
    intro q₁ q₂
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    intro h
    exact QuotientGroup.eq.2 ((hψ a b).1 h)
  have hsurj : Function.Surjective φ := by
    rintro ⟨O, hO⟩
    obtain ⟨F'', hEZ, hRep, rfl⟩ := hO
    obtain ⟨a', b, ν, m, hd⟩ := Formalism.L2.SG.Pf.TupActB.ontoCZ_holds M δ u u' F0 what₂ γ w F' L U hH F'' hEZ hRep
    have ha'd : IsUnit (a' : MatR D).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hd.1]; exact isUnit_one
    have hdet : IsUnit (L⁻¹ * (a' : MatR D) * L).det := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact ((Matrix.isUnit_nonsing_inv_det L hLd).mul ha'd).mul hLd
    let y : GLR D := Matrix.nonsingInvUnit (L⁻¹ * (a' : MatR D) * L) hdet
    have hy : ((y : GLR D) : MatR D) = L⁻¹ * (a' : MatR D) * L := rfl
    have hyC : y ∈ C := (Formalism.L2.SG.Pf.ZsVolGrp.mem_CZ M δ u u' _ L hLd y).2
      ((Formalism.L2.SG.Pf.ZsVolShape.mem_stZSet_iff M δ u u' hH.1 _ L y).2 ⟨a', hy, hd.1, b, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩)
    refine ⟨((⟨y, hyC⟩ : C) : C ⧸ S), ?_⟩
    show ψ ⟨y, hyC⟩ = _
    apply Subtype.ext
    show cls (F2 ⟨y, hyC⟩) = cls F''
    rw [hcls _ _ hEZ]
    refine (fibreIndex_holds M δ u u' F0 what₂ γ w F' L U hH (A ⟨y, hyC⟩) (Bm ⟨y, hyC⟩) (Nu ⟨y, hyC⟩) (Mu ⟨y, hyC⟩)
      (F2 ⟨y, hyC⟩) a' b ν m F'' y y (hAL ⟨y, hyC⟩) hy (hD ⟨y, hyC⟩) hd).2 ?_
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  refine ⟨C ⧸ S, inferInstance, ((1 : C) : C ⧸ S), MulAction.stabilizer_quotient S, ⟨?_⟩⟩
  exact (Set.equivOfEq (MulAction.orbit_eq_univ C ((1 : C) : C ⧸ S))).trans
    ((Equiv.Set.univ _).trans (Equiv.ofBijective φ ⟨hinj, hsurj⟩))

theorem orbitStabilizerIndex_holds : OrbStabE M δ u u' F0 what₂ (CZ M δ u u') :=
  Formalism.L2.SG.Pf.ZsVolOrb.orbStabE_of_act M δ u u' F0 what₂ (orbitAction_holds M δ u u' F0 what₂)

theorem volIdxProd_of_prodE (hP : PrimeHyp D u (Tu D u')) (h : ProdE M δ u u' F0 what₂ (CZ M δ u u')) :
    Formalism.L2.SG.Pf.Coef.VolIdxProd M δ u u' F0 what₂ :=
  volIdxProd_of M δ u u' F0 what₂ hP (CZ M δ u u') (orbitStabilizerIndex_holds M δ u u' F0 what₂) h

end Formalism.L2.SG.Pf.ZsVolAsm

end
end

section

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp



namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem lemmaG3_of_coefficients (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    nmlOf Y u u' t1 = nmlOf Y u u' t2 := by
  obtain ⟨iω, iς, i3⟩ := lemmaG3_of_inputs Y hT hT' t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hGF1 : Gflag (X.Fu u) t1.frame.fl ≠ 0 := G_ne_of_Gt Y h1
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  have hs'' := SRat_inv (lf D (X.Fu u')) hs'
  set ς := t1.lin * s'⁻¹ * t1.lin⁻¹ with hς
  have hςx : ∀ x, ς x = t1.lin (s'.symm (t1.lin.symm x)) := fun x => rfl
  have hςf : ∀ x ∈ t1.frame.fl.X, ς x - x ∈ t1.frame.fl.X := by
    intro x hx
    refine (mem_frameX Y t1 _).2 ?_
    have hx0 := (mem_frameX Y t1 x).1 hx
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply]
    exact Submodule.sub_mem _ (X_pres (lf D (X.Fu u')) hs''.2.1 _ hx0) hx0
  have hςz : ς t1.frame.fl.z - t1.frame.fl.z ∈ t1.frame.fl.X := by
    refine (mem_frameX Y t1 _).2 ?_
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply]
    exact hs''.2.2
  obtain ⟨τ, hτi, hτA, P1, P2⟩ := tau_exists (X.Fu u) t1.frame.fl hGF1 hTE (star_natCast _) hTE' (star_natCast _)
    σ ς hσ.1 (fun x hx => Submodule.sub_mem _ (X_pres (lf D (X.Fu u)) hσ.2.1 x hx) hx)
    (fun x hx => X_pres (lf D (X.Fu u)) hσ'.2.1 x hx) hσ.2.2 hςf hςz iω iς i3
  have hτX : ∀ x ∈ (X.Fu u).X, τ x = x := fun x hx => hτA x (X_le_Asp _ _ hx)
  have hτX1 : ∀ x ∈ t1.frame.fl.X, τ x = x := fun x hx => hτA x (by rw [← Asp_symm]; exact X_le_Asp _ _ hx)
  have hτs : ∀ x ∈ (X.Fu u).X, τ.symm x = x := fun x hx => by
    conv_lhs => rw [← hτX x hx]
    simp
  set n := σ * τ⁻¹ with hn
  set n' := t1.lin⁻¹ * τ * t1.lin * s' with hn'
  have hnN : n ∈ NRat (lf D (X.Fu u)) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem hσ.1 ((Formalism.HermitianLatticesTheory.isom _).inv_mem hτi), fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u).X := Xflag_le_X (lf D (X.Fu u)) (j + 1) hx
      show σ (τ.symm x) - x ∈ _
      rw [hτs x hxX]
      exact hσ.2.1 j x hx
    · have hτi' : τ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom _).inv_mem hτi
      have hz : τ.symm y ∈ orth (VS D) (Xsp (lf D (X.Fu u))) :=
        perp_pres (lf D (X.Fu u)) hτi' (fun x hx => by rw [LinearEquiv.symm_symm, hτX x hx]; exact hx) y hy
      have := P1 _ hz
      rw [LinearEquiv.apply_symm_apply] at this
      show σ (τ.symm y) - y ∈ _
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
  have hn'N : n' ∈ NRat (lf D (X.Fu u')) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem
      ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ1) hτi) hγ1) hs'.1, fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u').X := Xflag_le_X (lf D (X.Fu u')) (j + 1) hx
      have hsx : s' x ∈ (X.Fu u').X := X_pres (lf D (X.Fu u')) hs'.2.1 x hxX
      have h1x : t1.lin (s' x) ∈ t1.frame.fl.X := (mem_frameX Y t1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hsx)
      show t1.lin.symm (τ (t1.lin (s' x))) - x ∈ _
      rw [hτX1 _ h1x, LinearEquiv.symm_apply_apply]
      exact hs'.2.1 j x hx
    · have hsy : s' y ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) :=
        perp_pres (lf D (X.Fu u')) hs'.1 (fun x hx => X_pres (lf D (X.Fu u')) hs''.2.1 x hx) y hy
      have hv : t1.lin (s' y) ∈ Lat.orth (VS D) t1.frame.fl.X := by
        refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
        rw [show x = t1.lin (t1.lin.symm x) by simp, hγ1]
        exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hsy _ ((mem_frameX Y t1 x).1 hx)
      have h := P2 _ hv
      rw [hςx, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
      have h' := (mem_frameX Y t1 _).1 h
      rw [map_sub, LinearEquiv.symm_apply_apply] at h'
      exact h'
  have heq : t2.lin = n * t1.lin * n' := by
    rw [he, hn, hn']
    group
  ext δ
  constructor
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n⁻¹, NRat_mul _ hm (NRat_inv _ hnN), n'⁻¹ * m', NRat_mul _ (NRat_inv _ hn'N) hm', ?_⟩
    rw [heq]
    group
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n, NRat_mul _ hm hnN, n' * m', NRat_mul _ hn'N hm', ?_⟩
    rw [heq]
    group

theorem normalsLemmaG3_holds : UnitaryNormalVectorCount := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 hσs ha ha' => ?_⟩
  obtain ⟨σ, hσ, s', hs', he⟩ := hσs
  have hT : 3 ≤ Tu D u ∧ 3 ≤ Tu D u' := by
    clear * - hc
    unfold Ctx at hc
    obtain ⟨-, -, -, h3, h3', -⟩ := hc.2.1
    exact ⟨h3, h3'⟩
  exact lemmaG3_of_coefficients Y hT.1 hT.2 t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'

end Formalism.L2.SG.NGCut.NormalVectorPairings
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

theorem upper_qbar {q : FreeE w} (hu : upperM w q) : ¬ selfP w (qbar w q) ∧ ¬ upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : qbar w q = q := h.symm
    rw [this] at hu; exact lt_irrefl _ hu
  · exact lt_asymm hu h

theorem lower_qbar {q : FreeE w} (hs : ¬ selfP w q) (hu : ¬ upperM w q) : upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  rcases lt_or_eq_of_le (not_lt.1 hu) with h | h
  · exact h
  · exfalso; apply hs
    apply Subtype.ext
    have h2 : pinv w q.1.2 = q.1.1 := h.symm
    have h3 : q.1.2 = pinv w q.1.1 := by rw [← h2, pinv_pinv]
    simp only [qbar]
    rw [h2, ← h3]

theorem hgt_le (q : FreeE w) : hgt w q ≤ D.R.rS := by
  unfold hgt; have := q.1.2.isLt; omega

section Main

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

theorem sgq_cases (q : FreeE w) : sgq w q = (1 : D.host.E) ∨ sgq w q = -1 := sgm_cases q.1.1 q.1.2

theorem sgq_sq (q : FreeE w) : sgq w q * sgq w q = (1 : D.host.E) := by
  rcases sgq_cases w q with e | e <;> rw [e] <;> ring

include hA in
theorem sg_dd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ ddPow D h) :
    sgq w q * D.conjF x ∈ ddPow D h := by
  have := dd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

include hA in
theorem sg_qd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ qdPow D h) :
    sgq w q * D.conjF x ∈ qdPow D h := by
  have := qd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

theorem gS_mul_qd (h : ℕ) {x : D.host.E} (hx : x ∈ ddPow D h) : ((gS D : ℕ) : D.host.E) * x ∈ qdPow D h := by
  rw [qdPow_mem_iff, mul_div_cancel_left₀ _ gS_ne]; exact hx

theorem nat_mul_mem (I : FI D) (m : ℕ) {x : D.host.E} (hx : x ∈ I) : (m : D.host.E) * x ∈ I := by
  rw [← nsmul_eq_mul]; exact (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubmonoid.nsmul_mem hx m

theorem self_id (s y c E : D.host.E) (m : ℕ) (hs : s * s = 1) (hsc : D.conjF s = s)
    (hE : E = y - s * D.conjF (c - y)) :
    (y - (m : D.host.E) * c) + s * D.conjF (y - (m : D.host.E) * c) =
      E + (s * D.conjF E - E) - (m : D.host.E) * (s * D.conjF E - E) + (1 - 2 * (m : D.host.E)) * c := by
  subst hE
  simp only [map_sub, map_mul, map_natCast, Formalism.MainNotions.BridgeLemma.conjF_inv, hsc]
  linear_combination (1 - (m : D.host.E)) * (c - y) * hs

end Main

end Formalism.L2.SG.Pf.StabIntLat
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
  {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem bwdTerm'_of_gx (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of' (btOK_holds Zd) hGX

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
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

theorem conjugator_mem_unipotent (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    g0 M δ hA L U hL hU ∈ UP p :=
  ⟨lOf_loUni M δ hA L U hL hU, ρOf_upUni M δ hA L U hL hU⟩

theorem H_le_UP (X : MP p) : KP M p ⊓ StabX p X ≤ UP p := fun h hh =>
  ⟨Formalism.L2.SG.Pf.ProdEP2Cut.loUni_of_int M hh.1.1, Formalism.L2.SG.Pf.ProdEP2Cut.upUni_of_int M hh.1.2⟩

theorem XP_eq (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    XP M δ u u' w L U = g0 M δ hA L U hL hU • Y0 M δ u u' w p := rfl

theorem mem_Ag_iff (x : GG p) : x ∈ Ag M δ u u' (p := p) w ↔ x ∈ StP M δ u u' w p ∧ x ∈ KP M p := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h1⟩, h2, rfl⟩

end Formalism.L2.SG.Pf.CountAt
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}

def uLo (X : MP p) (h1 : ∀ a b, a < b → X a b = 0) (h2 : ∀ a, X a a = 1) : GLp p :=
  Matrix.nonsingInvUnit X (by rw [Formalism.L2.SG.Pf.FibQ.det_lower p h1 h2]; exact isUnit_one)

def uUpU (X : MP p) (h1 : ∀ a b, b < a → X a b = 0) (h2 : ∀ a, X a a = 1) : GLp p :=
  Matrix.nonsingInvUnit X (by rw [Formalism.L2.SG.Pf.FibQ.det_upper p h1 h2]; exact isUnit_one)

def pairOfU (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
    (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (x : UP p) (hx : πa x = 1) :
    Formalism.L2.SG.Pf.Coef.CellPair a :=
  ⟨(((x : GG p).1 : GLp p).val, (((x : GG p).2.unop : GLp p)).val),
    by
      obtain ⟨h1, h2⟩ := (hker x).1 hx
      exact ⟨fun i => (h1 i i).2 rfl, fun i j hij => (h1 i j).1 hij, fun i j hij hb => h2 i j hij hb⟩,
    fun i => (x.2.2 i i).2 rfl, fun i j hij => (x.2.2 i j).1 hij⟩

end Formalism.L2.SG.Pf.CountAt
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc

namespace Formalism.L2.SG.RowsConc

theorem normExpSatTied_holds : NormExpSatTied := by
  intro D X Y u u' hT
  have hF := Formalism.L2.SG.Closed.FundExistsC_holds D X Y u u'
  have hO : ∀ w, Formalism.L2.SG.WuDecay.FoldOK X w Y.hK :=
    fun w => Formalism.L2.SG.Closed.FoldOKC_outright D X Y w hT.1 hT.2.2.2.2.1
  have hI := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u' (hO u) (hO u') hF
  have hAbs := absConvTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.AbsConvC_outright D X Y u u' hT
  exact Formalism.L2.SG.NormCut.normExpSatC'_of_PD (fun D => Formalism.L2.SG.Pf.positive_definite_isomorphism D) D X Y u u' hI
    (Formalism.L2.SG.Closed.AmpWellDefC_holds D X Y u u' hI) (Formalism.L2.SG.Closed.OOFundIndepC_holds D X Y u u' hF hI) hAbs

theorem idOneC_holds : IdOneC :=
  idOneC_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.IdCellDiagC_holds

end Formalism.L2.SG.RowsConc
end
end
