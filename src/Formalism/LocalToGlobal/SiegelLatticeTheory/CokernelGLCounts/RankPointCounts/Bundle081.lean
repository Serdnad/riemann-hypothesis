module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameEntry
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle076
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle023
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle043
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle067
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048

@[expose] public section

section

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRelPf

def ofPts {K : Type} {i : ℕ} (s : Σ c : Composition (i + 1), (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn fun a => (s.2 a, s.1.blocksFun a)

theorem ofPts_toPts {K : Type} [Zero K] {i : ℕ} (p : Point K (i + 1)) : ofPts (toPts p) = p.1 := by
  apply List.ext_get
  · simp [ofPts, toPts, Composition.length]
  · intro n h1 h2
    simp [ofPts, toPts, Composition.blocksFun]

theorem toPts_injective {K : Type} [Zero K] {i : ℕ} :
    Function.Injective (toPts : Point K (i + 1) → Σ c : Composition (i + 1), (Fin c.length → K)) := by
  intro p q h
  apply Subtype.ext
  rw [← ofPts_toPts p, ← ofPts_toPts q, h]

end Formalism.L2.SG.Pf.FormRelPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel Formalism.L2.SG.Pf.FormRelPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formRelC_of (hRD : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.Pf.RowForm.RealDecompC X Y u u')
    (hRC : Formalism.L2.SG.Pf.RelCharC) : FormRelC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ ν hν t ht hv => ?_⟩
  have hG : t.G ≠ 0 := Formalism.L2.SG.Pf.RowForm.realDecomp_G_ne X Y u u' t ht
  have hrel : t.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨hpt, hall⟩ := hRD D X Y u u' t hrel hG
  refine ⟨⟨_, rfl, hpt⟩, fun w hw hwr => ?_⟩
  have hw' : w = Formalism.L2.SG.PairVal.ptOf t.toTerm := toPts_injective hw
  subst hw'
  have hγ := Formalism.L2.SG.Pf.RowForm.isPtRep_gamW X u u' hwr
  obtain ⟨g, hg, g', hg', hdec⟩ := hall _ hγ
  obtain ⟨c, hc⟩ := formTransp_any (X := X) (Y := Y) (u := u) (u' := u') (νq := ν) hν.2 hRC t hrel hwr g hg g' hg'
    hdec
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have := FiniteDimensional.complete ℂ (X.Vpi u')
  refine ⟨(c : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g')),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'), ?_⟩
  rw [hc, hdec, Formalism.L2.SG.Pf.RowForm.ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' (X.psiInfU u g) (X.psiInfU u' g')
    (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg) (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg')
    (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x), ← Complex.coe_smul, smul_smul]

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem conj_ddPow (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) {k : ℕ} (hk : k ≤ D.R.rS) {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    D.conjF x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have hLG := Formalism.L2.SG.Pf.StabIntSh.locGlob (D := D)
  have hne := (Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)).1 k
  exact (hLG _ hne _).1 fun p => Formalism.L2.SG.Pf.StabIntSh.locMem_conj δ M hA p hk ((hLG _ hne _).2 hx p)

theorem conj_qdPow (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) {k : ℕ} (hk : k ≤ D.R.rS) {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k) :
    D.conjF x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k := by
  unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at *
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨D.conjF z, conj_ddPow δ M hA hk hz, ?_⟩
  rw [map_mul]
  congr 1
  simp

theorem bt_sgn (uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (j i : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.StabIntSh.bt D (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) j i = uu' j i := by
  unfold Formalism.L2.SG.Pf.StabIntSh.bt Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h1 : ((-1 : D.host.E) ^ (D.R.rS - j.val)) * (-1) ^ (D.R.rS - j.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have h2 : ((-1 : D.host.E) ^ (D.R.rS - i.val)) * (-1) ^ (D.R.rS - i.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (uu' j i * (-1) ^ (D.R.rS - i.val) * (-1) ^ (D.R.rS - i.val)) * h1 + uu' j i * h2

theorem star_conjF (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  exact Formalism.BasicNotions.Examples₂.star_eq_conj D.host x

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem frameShape_holds : Formalism.L2.SG.Pf.ZsVolIn.FrameShapeP M δ u u' F0 what₂ := by
  intro γ w F' L U hH s hs uu uu' huu huu' hfr hfr'
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨⟨⟨hLift', _, hFOK⟩, _⟩, hAdm, _, _, _⟩ := hN
  obtain ⟨_, ⟨_, _, hLift, hConv⟩, hXF⟩ := hR.1 γ.lam γ.mem
  have hsΛ : ∀ v ∈ γ.lam, s v ∈ γ.lam := fun v hv => by
    have h := hs.1.1.2
    rw [← h]
    exact Submodule.mem_map_of_mem hv
  have hadm : ∀ b, ModG (VS D) γ.lam (Lat.gS D) (F'.fl.fvec b - (lf D F0).fl.fvec b) := by
    intro b
    have h := hAdm.2.2 b
    convert h using 3
    simp [frameAct, Matrix.one_apply]
    rfl
  intro i j hji
  have hk : ((i : ℕ) - (j : ℕ)) ≤ D.R.rS := by have := i.2; omega
  have h1 := frame_entry (lf D F0) γ.lam hXF hLift.1 s hsΛ uu huu hfr j i hji
  have h2 := frame_entry F' γ.lam hFOK.2 hLift'.1 s hsΛ uu' huu' hfr' j i hji
  have h3 := cong_glob (lf D F0) F' γ.lam hConv hFOK.1 hXF hFOK.2 hLift.1 hLift'.1 hadm s hsΛ uu uu' huu huu' hfr hfr' j i hji
  rw [Matrix.conjTranspose_apply, bt_sgn, star_conjF]
  refine ⟨conj_ddPow δ M hA hk h1, h2, ?_⟩
  rw [← map_sub]
  exact conj_qdPow δ M hA hk h3

end Formalism.L2.SG.Pf.ZsVolLat

end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frameAct_one {n : ℕ} (f : Fin n → (VS D).V) (b : Fin n) : frameAct f 1 b = f b := by
  simp [frameAct, Matrix.one_apply]

theorem sgnP_mem (p : PlF D) (b : Fin (D.R.rS + 1)) : TermLoc.sgnP D p b ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  refine ⟨Polynomial.X ^ 2 - 1, by monicity!, ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
  rw [pow_two, TermLoc.localSign_sq, sub_self]



theorem btAdm : BtAdm Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, _⟩ := hs
  refine ⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun b => ?_⟩
  intro P hgP
  rw [frameAct_one]
  haveI := P.isPrime
  set x : (VS D).V := frame (liftF F'₂) b - frame (lf D F0) b with hx
  obtain ⟨p, hpdef⟩ : ∃ p : PlF D, p = Formalism.L2.SG.Pf.LocalDenominators.plOf P.asIdeal P.isMaximal := ⟨_, rfl⟩
  have hPp : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal := by rw [hpdef]; rfl
  have hty : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) :=
    (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P hPp).1 hgP
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 ((D.s_split p).2 hty)
  have hag := (Zd.agree p).2.2.2.2.2
  obtain ⟨g', hMs⟩ : ∃ g', (Zd.M p).split = some g' := by
    cases hm : (Zd.M p).split with
    | none => rw [hm, hsg] at hag; exact hag.elim
    | some g' => exact ⟨g', rfl⟩
  have hadm := ((hloc p).1.1.2.2.2.2.2 g' hMs).2.2 b

  have hrow := hC.2.1.1 γ.lam γ.mem
  have hgP' : ∀ P' : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      P'.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P'.asIdeal :=
    fun P' hP' => (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P' hP').2 hty
  obtain ⟨-, w, hw, hw1⟩ := Formalism.L2.SG.Pf.BBTie.bt_typed_frFac Zd (Formalism.L2.SG.Pf.locEqC_holds D Zd)
    (Formalism.L2.SG.Pf.locDiffC_holds D Zd) p F0 γ.lam hrow.2.1.1.fg hrow.2.2 hrow.2.1.2.2.2 hgP' b
  have hO := (Zd.agree p).2.2.2.1
  have hsg' : TermLoc.sgnP' D p b = TermLoc.sgnP D p b := by
    show (match (D.s.atP p).split with | some _ => TermLoc.sgnP D p b | none => (-1) ^ (D.R.rS - b.val)) = _
    rw [hsg]
  set c : (D.s.atP p).Ep := TermLoc.sgnP D p b * frFac Zd.δ p b with hc
  have hdiff : locF' Zd p F'₂ b - (tLoc Zd p γ).f b = c • baseChange₂ D p x := by
    show (TermLoc.sgnP' D p b * frFac Zd.δ p b) • baseChange₂ D p (frame F'₂ b) -
      (TermLoc.sgnP D p b * frFac Zd.δ p b) • baseChange₂ D p (frame (lf D F0) b) = _
    rw [hsg', hx, map_sub, smul_sub]
    rfl
  have hinv : (TermLoc.sgnP D p b * w) * c = 1 := by
    rw [hc, mul_mul_mul_comm, TermLoc.localSign_sq, hw1, one_mul]
  have hinvO : TermLoc.sgnP D p b * w ∈ (Zd.M p).L.O := by
    rw [hO]; exact (D.s.atP p).O.mul_mem (sgnP_mem p b) (by rw [← hO]; exact hw)

  have h1 : baseChange₂ D p x ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g'.q : (D.s.atP p).Fp))
      (lattice₂ D Zd.M p Λ₂) := by
    have : baseChange₂ D p x = (TermLoc.sgnP D p b * w) • (locF' Zd p F'₂ b - (tLoc Zd p γ).f b) := by
      rw [hdiff, smul_smul, hinv, one_smul]
    rw [this]
    exact Submodule.smul_mem _ ⟨_, hinvO⟩ hadm

  have hqg := Formalism.L2.SG.Pf.Cnt.DualityBasisChange.q_gS_inv_mem Zd.agree p hMs
  have h2 : (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ₂ := by
    have key : ∀ v ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g'.q : (D.s.atP p).Fp))
        (lattice₂ D Zd.M p Λ₂), (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • v ∈ lattice₂ D Zd.M p Λ₂ := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨y, hy, rfl⟩ := hv
        rw [smul_smul]
        exact (lattice₂ D Zd.M p Λ₂).smul_mem ⟨_, hqg⟩ hy
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => rw [smul_add]; exact Submodule.add_mem _ ha hc
      | smul o v _ hv =>
        have e : (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • (o • v) =
            o • ((D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • v) := by
          show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
          rw [smul_smul, smul_smul, mul_comm]
        rw [e]; exact Submodule.smul_mem _ _ hv
    exact key _ h1
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have := Formalism.L2.SG.Pf.Cnt.DualityBasisChange.gS_ne (D := D); exact_mod_cast this
  have h3 : baseChange₂ D p ((((gS D : ℕ) : D.host.E))⁻¹ • x) ∈ lattice₂ D Zd.M p Λ₂ := by
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact h2
  haveI := p.isPrime
  letI := hlat
  have h4 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ₂) (by infer_instance) _).1 h3
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ₂ _).1 h4
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, fun h => ht (by rw [← hPp]; exact h), ?_⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x =
      ((gS D : ℕ) : 𝓞 D.host.E) • (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • ((((gS D : ℕ) : D.host.E))⁻¹ • x)) := by
    rw [Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ₂
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) htx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section IntM

variable {K : Type*} [CommRing K] (I : Subring K) {n : ℕ}

theorem int_mul {A B : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    ∀ i j, (A * B) i j ∈ I := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem (hA i k) (hB k j)

theorem int_diag {d : Fin n → K} (hd : ∀ a, d a ∈ I) : ∀ i j, Matrix.diagonal d i j ∈ I := by
  intro i j
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact I.zero_mem

end IntM

section Good

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem gY_int (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) {U₁ X' : PairVal.MatR D} (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O)
    (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) :
    ∀ i j, ((gY w U₁ X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
  have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hcm : ∀ i j, ((cOf (fσ w) (fun a => pv w.1 a) X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    simp only [Matrix.map_apply, cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hν' _) (hX _ _)) (hν _)
  have hci : ∀ i j, (((cOf (fσ w) (fun a => pv w.1 a) X')⁻¹).map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    rw [ZsVolGrp.inv_eq_adj (det_up' hc)]
    have e := RingHom.map_adjugate (D.s.atP p).ιE (cOf (fσ w) (fun a => pv w.1 a) X')
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at e
    rw [e]
    exact ZsVolGrp.adj_mem (D.s.atP p).O hcm i j
  simp only [gY, Matrix.map_mul]
  exact int_mul _ (int_mul _ hU' hci) hU

theorem good_at (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {L₁ U₁ A₀ B₀ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX' : IsLo X') (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0)
    (hcf : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O)
    (hcfi : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O)
    (hA : ∀ i j, (D.s.atP p).ιE (A₀ i j) ∈ (D.s.atP p).O) (hB : ∀ i j, (D.s.atP p).ιE (B₀ i j) ∈ (D.s.atP p).O)
    (hL : ∀ i j, (D.s.atP p).ιE (L₁ i j) ∈ (D.s.atP p).O) (hL' : ∀ i j, (D.s.atP p).ιE (L₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O) (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) : GoodAt Zd p w L₁ U₁ A₀ B₀ X' := by
  obtain ⟨hgX, hgY, -⟩ : IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧ True := by
    have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
    have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
    have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
    exact ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, trivial⟩
  have hgYi := gY_int p w hX' hpat hU hU' hν hν' hX
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  have hlo := locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  have hup := locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  refine ⟨⟨hlo.1, hlo.2, fun i j => ?_⟩, ⟨hup.1, fun a b hab => hup.2 b a hab, fun i j => ?_⟩⟩
  · rw [hR, locL_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcf) ?_) (int_diag _ hcfi) i j
    simp only [gX, Matrix.map_mul]
    exact int_mul _ hA (int_mul _ (int_mul _ hL hX) hL')
  · rw [hR, locR_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcfi) ?_) (int_diag _ hcf) i j
    rw [Matrix.map_mul]
    exact int_mul _ hgYi hB

end Good

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.CountBase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.AtPt
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem zhatOM_sg (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ZhatOM X * Sg D.host.E D.R.rS = X := by
  ext a b
  simp only [ZhatOM, Sg, Matrix.mul_diagonal]
  rw [mul_comm, ← mul_assoc, ← mul_pow]
  simp

theorem modMat_ord (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) (hM : (M p).split = none)
    (w : Point D.host.E (D.R.rS + 1)) :
    Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) *
        (ptMat w).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) =
      modMat δ T T' p w := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := by
    have h := (hA p).2.2.2.2.2
    rw [hM] at h
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  ext a b
  rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
  by_cases hb : b = sgF w a
  · rw [if_pos hb, if_pos hb, modMat_blk Zd]
    simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul]
    subst hb
    ring
  · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]

theorem baseConj_L (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (hM : (M p).split = none) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    Formalism.L2.SG.Pf.ProdE.Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w = a.mat := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hY := Formalism.L2.SG.Pf.PCount.zzp_sgn_ord Zd u u' p hM (ZhatOM (ptMat w))
  rw [zhatOM_sg] at hY
  have hmat := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  rw [hmat]
  unfold Formalism.L2.SG.Pf.ProdE.Y0
  congr 1
  rw [show Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p =
    Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p from rfl, hY]
  exact modMat_ord hA _ _ p hM w

end Formalism.L2.SG.Pf.CountBase
end
end
