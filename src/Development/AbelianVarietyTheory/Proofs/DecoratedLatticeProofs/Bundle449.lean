module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle374
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle427
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPin



theorem exists_levelData : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k), SymRead W l S → (∀ PP, LocY (l PP) y v.N (pk W).βY b fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc) → (∀ PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((l PP).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (l PP).FT) → ∃ JG eG eGT dG, ∃ (n : ℕ) (G : Fin n → GLoc { v with JG := JG, eG := eG, eGT := eGT, dG := dG }) (pl : Fin n ≃ (pk W).Pg), GPin G ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eG j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) (dG j) ∧ ∀ h, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eGT j h)) ∧ (∀ j row col, GRead (⟨mkGeo m b, j, row, col⟩ : FamCh W u) G pl) ∧ ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (G i).FT ∧ (G i).z₀ = fun r => (ofSplit (G i).q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ a y m b v hc hτ hNT hgP hTP l S hSym hY hStd
  classical
  have hψ : IsStdChar D (pk W).ψ (-1) := hc.std
  choose ν hν using fun PP : (pk W).Pg => GlobalTheory.SplitWeil.exists_isUnitVol (l PP).k
  choose eg egT cg heg hegT hcm hcp hct sEg sCg using fun PP => exists_locComb (l PP) (S PP) (hY PP) (ν PP) hψ
  have hPv : ∀ PP : (pk W).Pg, (l PP).q.v ∈ v.gP := fun PP => (hgP _).2 ⟨PP.1, PP.2, (l PP).under⟩
  let n := Fintype.card (pk W).Pg
  let pl : Fin n ≃ (pk W).Pg := (Fintype.equivFin _).symm

  have hEG : ∀ j, ∃ c' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (eg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => eg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sEg (pl i) j w hw)) _
  choose eG hEGs hEGf using hEG
  have hDG : ∀ j, ∃ c' : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (cg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => cg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sCg (pl i) j w hw)) _
  choose dG hDGs hDGf using hDG
  have hsj : ∀ (i : Fin n) (j : ℕ), j + 2 * 0 + 2 = D.R.m → (l (pl i)).s = j := fun i j h => by
    have := (l (pl i)).hs
    omega
  let eT : ∀ (i : Fin n) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m), WO (Yc D (j + 1)) D.sp.X' →₀ ℂ := fun i j h =>
    cast (congrArg (fun n' => WO (Yc D (n' + 1)) D.sp.X' →₀ ℂ) (hsj i j h)) (egT (pl i))
  have hEGT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ,
      (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (eT i j h) f') f := fun j h =>
    exists_fold _ _ _ _ (fun i => eT i j h) (fun i => mxAt_cast (F := fun n' => Yc D (n' + 1)) (hsj i j h) _
      (fun w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w ((hegT (pl i)).1 w hw))) _
  choose eGT hEGTs hEGTf using hEGT

  let JG : ∀ j, Subgroup (GA D (Yc D j)) := fun j => GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ v.gP) ⊓
    ⨅ (i : Fin n) (a' : ℕ) (ha : j + a' = (l (pl i)).s + 1),
      frameSub ((GeneralLinearGroup.map (l (pl i)).q.pr).comp (matHom (Yc D j))) ((hY (pl i)).FY j a' ha)
        ((((S (pl i)).T (Fin D.R.t)).lev j a' ha).J)
  let v' : VCom (commOf (pk W) u (mkGeo m b)) := { v with JG := JG, eG := eG, eGT := eGT, dG := dG }
  let G : Fin n → GLoc v' := fun i =>
    { k := (l (pl i)).k
      ν := ν (pl i)
      unitVol := hν (pl i)
      q := (l (pl i)).q
      unit := (l (pl i)).unit
      s := (l (pl i)).s
      hs := (l (pl i)).hs
      S := S (pl i)
      char := hSym.char (pl i)
      FX := (l (pl i)).FX
      FT := (l (pl i)).FT
      FM := (l (pl i)).FM
      FY := (hY (pl i)).FY
      sc := (hY (pl i)).sc
      sc_unit := (hY (pl i)).sc_unit
      sc_step := (hY (pl i)).sc_step
      hz_unit := (hY (pl i)).hz_unit
      bes := (hY (pl i)).bes
      jac := (hY (pl i)).jac
      z₀ := fun r => (ofSplit (l (pl i)).q).pr (a.ζ₀ r)
      last := (l (pl i)).last
      tau := fun h => by
        rw [show v'.τ = y.τ from hτ]
        exact (hY (pl i)).tau h
      latX := (l (pl i)).latX
      latM := (l (pl i)).latM
      latY := (hY (pl i)).latY
      latT := by
        rw [show v'.NT = a.LT from hNT]
        exact (l (pl i)).latT
      eg := eg (pl i)
      eg_is := heg (pl i)
      egT := egT (pl i)
      egT_is := hegT (pl i)
      cg := cg (pl i)
      cg_mid := hcm (pl i)
      cg_pen := hcp (pl i)
      cg_top := hct (pl i) }
  refine ⟨JG, eG, eGT, dG, n, G, pl, ?_, fun j => ⟨hEGs j, hDGs j, hEGTs j⟩, ?_, fun i => ⟨(hStd (pl i)).1, (hStd (pl i)).2, rfl⟩⟩

  · refine ⟨fun i i' h => pl.injective (Subtype.ext (under_inj hTP (pl i).2 (pl i').2 ?_)), fun p => ?_, fun j _ g => ?_,
      fun j _ f _ => hEGf j f, fun j h => ⟨fun i => eT i j h, fun i => cast_heq _ _, fun f _ => hEGTf j h f⟩,
      fun j _ f _ => hDGf j f⟩
    · have e1 := (l (pl i)).under
      have e2 := (l (pl i')).under
      change (l (pl i)).q.v = (l (pl i')).q.v at h
      rw [← e1, ← e2, h]
    · change p ∈ v.gP ↔ ∃ i, p = (l (pl i)).q.v
      rw [hgP]
      constructor
      · rintro ⟨PP, hPP, rfl⟩
        refine ⟨pl.symm ⟨PP, hPP⟩, ?_⟩
        rw [(l _).under, Equiv.apply_symm_apply]
      · rintro ⟨i, rfl⟩
        exact ⟨(pl i).1, (pl i).2, (l _).under⟩
    · change g ∈ JG j ↔ _
      simp only [JG, Subgroup.mem_inf, Subgroup.mem_iInf, mem_frameSub]
      rfl
  · intro j row col
    refine ⟨fun i => ⟨(l (pl i)).idem, (l (pl i)).under⟩, fun i j h1 h2 => hSym.mu (pl i) j h1 h2,
      fun i j c hc => (hY (pl i)).frame j c hc, fun i => (l (pl i)).frameTop, fun g => ⟨?_, ?_⟩⟩
    · rw [hSym.grp g]
      constructor
      · intro h i
        exact h (pl i)
      · intro h PP
        obtain ⟨i, rfl⟩ := pl.surjective PP
        exact h i
    · intro hg x hx
      rw [hSym.chr g hg (Equiv.piCongrLeft (fun PP => (S PP).P.J) pl x) (fun PP => ?_)]
      · rw [← Equiv.prod_comp pl]
        simp only [Equiv.piCongrLeft_apply_apply]
        rfl
      · obtain ⟨i, rfl⟩ := pl.surjective PP
        rw [Equiv.piCongrLeft_apply_apply]
        exact hx i

end GlobalTheory.LevPin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.LevProd.OffTwist

theorem entry_mem_of_stab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) (L : Submodule (𝓞 E) (Fin n → E))
    (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ s, (Pi.single s (T : E) : Fin n → E) ∈ L)
    {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ Formalism.UG.levelVL σ J v L) (r s : Fin n) :
    g.val r s ∈ intV E v := by
  replace hg : g ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L) := hg.2
  have hle : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L, ∀ j, y j ∈ intV E v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      intro j
      obtain ⟨c, hc⟩ := h1 x hx j
      refine Subring.subset_closure (Or.inl ⟨⟨x j, c, hc.symm⟩, rfl⟩)
    | zero => intro j; exact zero_mem _
    | add x y _ _ hx hy => intro j; exact add_mem (hx j) (hy j)
    | smul c x _ hx => intro j; exact mul_mem c.2 (hx j)
  have hv : Valued.v ((T : ℕ) : v.adicCompletion F) = 1 := by
    have e : ((T : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (T : 𝓞 F)) := by
      simp
    rw [e]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hT
  have hne : ((T : ℕ) : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact zero_ne_one hv
  have hinv : ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have hc : (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨_, hinv⟩, rfl⟩)
  have hmem : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s (T : E) : Fin n → E) i)) ∈
      Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L := Submodule.subset_span ⟨_, h2 s, rfl⟩
  have h3 := hle _ ((hg _).1 hmem) r
  have e3 : (g.val *ᵥ fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s (T : E) : Fin n → E) i)) r =
      g.val r s * (T : ℕ) := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [e3] at h3
  have e4 : ((T : ℕ) : E ⊗[F] v.adicCompletion F) * ((1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹) = 1 := by
    have : ((T : ℕ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F) :=
      (map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)) T).symm
    rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hne]
    rfl
  have h4 := mul_mem h3 hc
  rwa [mul_assoc, e4, mul_one] at h4

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prV_toEAf (v : GlobalTheory.FinPl.Pl D) (x : AE D) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D x) =
      Algebra.TensorProduct.comm D.host.F _ _ (GlobalTheory.FinPl.compAt D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero, map_zero]
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, map_add (f := _)]

theorem pr_eq_zero (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (hx : Formalism.UG.prV (E := D.host.E) q.v (toEAf D x) = 0) : q.pr x = 0 := by
  rw [prV_toEAf, map_eq_zero_iff _ (AlgEquiv.injective _)] at hx
  have h1 : GlobalTheory.FinPlLoc.idem D (· = q.v) * x = 0 := by
    rw [← GlobalTheory.FinPlLoc.mem_idOff_iff]
    refine (Submodule.mem_iInf _).2 ?_
    rintro ⟨w, rfl⟩
    exact RingHom.mem_ker.2 hx
  have he := (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.e_mem_idAt q)
  have h2 : q.sec (q.pr x) = 0 := by
    rw [q.sec_pr, ← he, mul_comm (GlobalTheory.FinPlLoc.idem D _), mul_assoc, h1, mul_zero]
  rw [← q.pr_sec (q.pr x), h2, map_zero]



theorem exists_int_lift (v : GlobalTheory.FinPl.Pl D) (y : D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) (hy : y ∈ intV D.host.E v) :
    ∃ x : AE D, finPart D x ∈ intAE D ∧ Formalism.UG.prV (E := D.host.E) v (toEAf D x) = y := by
  have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  induction hy using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨c, rfl⟩
    · refine ⟨(1 : AF D.host.F) ⊗ₜ (c : D.host.E), AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩, rfl⟩
    · let α : Af D.host.F := RestrictedProduct.mk (Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F)
        (Filter.Eventually.of_forall fun w => by
          by_cases h : w = v
          · subst h; rw [Pi.single_eq_same]; exact c.2
          · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
      have hα : α ∈ intAf D.host.F := fun w => by
        show (Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F) w ∈ _
        by_cases h : w = v
        · subst h; rw [Pi.single_eq_same]; exact c.2
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      refine ⟨pairA D.host.F 0 α ⊗ₜ (1 : D.host.E), ?_, ?_⟩
      · rw [GlobalTheory.FinPlLoc.finPart_pair]
        exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩
      · rw [prV_toEAf, GlobalTheory.FinPlLoc.compAt_pair, Algebra.TensorProduct.comm_tmul]
        show (1 : D.host.E) ⊗ₜ[D.host.F] ((Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F) v) = _
        rw [Pi.single_eq_same]
  | zero => exact ⟨0, by rw [RingHom.map_zero]; exact zero_mem _, by rw [RingHom.map_zero, RingHom.map_zero]⟩
  | one =>
    refine ⟨1, ?_, by rw [RingHom.map_one, RingHom.map_one]⟩
    rw [RingHom.map_one, Algebra.TensorProduct.one_def]
    exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, by rw [RingHom.map_add (f := _)]; exact add_mem hx hy, by rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]⟩
  | neg a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨-x, by rw [RingHom.map_neg]; exact neg_mem hx, by rw [RingHom.map_neg, RingHom.map_neg]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x * y, by rw [RingHom.map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE hx hy, by rw [RingHom.map_mul, RingHom.map_mul]⟩

theorem pr_mem_int (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (hx : Formalism.UG.prV (E := D.host.E) q.v (toEAf D x) ∈ intV D.host.E q.v) :
    q.pr x ∈ 𝒪[k] := by
  obtain ⟨x', h1, h2⟩ := exists_int_lift q.v _ hx
  have h3 : q.pr (x - x') = 0 := pr_eq_zero q _ (by rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self])
  rw [RingHom.map_sub, sub_eq_zero] at h3
  rw [h3, q.int_iff, q.sec_pr, RingHom.map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE ?_ h1
  have := (q.int_iff 1).1 (one_mem _)
  rwa [← map_one q.pr, q.sec_pr, mul_one] at this

theorem conj_int {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] {pos : Y → ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (hF : IsStdFr pos F)
    (M : Matrix (Fin N) (Fin N) k) (hM : ∀ r s, M r s ∈ 𝒪[k]) (a b : Y) : (F.γ * M * F.β) a b ∈ 𝒪[k] := by
  obtain ⟨e, -, he⟩ := hF
  have hγ : F.γ = (1 : Matrix (Fin N) (Fin N) k).submatrix e id := by
    have h1 : (1 : Matrix (Fin N) (Fin N) k).submatrix e id * F.β = 1 := by
      rw [he, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one, Matrix.submatrix_one_equiv]
    rw [← Matrix.one_mul F.γ, ← h1, Matrix.mul_assoc, F.βγ, Matrix.mul_one]
  have h : F.γ * M * F.β = M.submatrix e e := by
    rw [hγ, he]
    conv_lhs => rw [← Matrix.submatrix_id_id M]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.one_mul, Matrix.mul_one]
  rw [h]
  exact hM _ _

theorem locHom_mem_KO (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) {n : ℕ} (hn : S.rank = n) {Y : Type} [Fintype Y] [DecidableEq Y]
    {pos : Y → ℕ} (F : GlobalTheory.LocMod.Frame k S.rank Y) (hF : IsStdFr pos F) (T : ℕ) (hT : (T : 𝓞 D.host.F) ∉ q.v.asIdeal)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (h2 : ∀ s, (Pi.single s (T : D.host.E) : Fin n → D.host.E) ∈ L) {σ : D.host.E →ₐ[D.host.F] D.host.E}
    {J : Matrix (Fin n) (Fin n) D.host.E} (U : Subgroup (GA D S))
    (hU : ∀ g ∈ U, ∃ κ : GL (Fin n) (EF D), κ.val = finM S hn g ∧ Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) q.v) κ ∈
      Formalism.UG.levelVL σ J q.v L) :
    ∀ g ∈ U, GlobalTheory.LevIdx.locHom q S F g ∈ KO k Y := by
  subst hn
  have key : ∀ g ∈ U, ∀ a b, (GlobalTheory.LevIdx.locHom q S F g).val a b ∈ 𝒪[k] := by
    intro g hg
    obtain ⟨κ, hκ, hs⟩ := hU g hg
    refine conj_int F hF _ fun r s => ?_
    have h := entry_mem_of_stab q.v T hT L h1 h2 _ hs r s
    have e : (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) q.v) κ).val r s =
        Formalism.UG.prV (E := D.host.E) q.v (toEAf D (mt S g r s)) := by
      show Formalism.UG.prV (E := D.host.E) q.v (κ.val r s) = _
      rw [hκ]; rfl
    rw [e] at h
    exact pr_mem_int q _ h
  intro g hg
  rw [GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv]
  exact ⟨key g hg, key _ (inv_mem hg)⟩

end GlobalTheory.LevProd.OffTwist

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.ClsKLive

theorem kval : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  intro j hj hab φ hφ Fv hV hval γ a' y'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hinj : Function.Injective (ι j) := hP.live.inj j
  have hram := ((hP.ram j hj.le φ).1 hφ).2
  let Fc : (I.chain l u a).cls j → PY (I.rec7 l Z).what₂.Tau (B.R.N j) := fun c =>
    if h : ∃ β, A.chOf j c = ι j β then Fv h.choose ⟨c, h.choose_spec⟩ else 0
  have hFcEq : ∀ β (c : {c // A.chOf j c = ι j β}), Fc c.1 = Fv β c := by
    intro β c
    have h : ∃ β, A.chOf j c.1 = ι j β := ⟨β, c.2⟩
    have hb : h.choose = β := hinj (h.choose_spec.symm.trans c.2)
    have gen : ∀ β' (hβ' : A.chOf j c.1 = ι j β'), β' = β → Fv β' ⟨c.1, hβ'⟩ = Fv β c := by
      rintro β' hβ' rfl; rfl
    simp only [Fc, dif_pos h]
    exact gen _ _ hb
  have hFc : ∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp j τ) := by
    intro c y
    by_cases h : ∃ β, A.chOf j c = ι j β
    · obtain ⟨β, hβ⟩ := h
      rw [hFcEq β ⟨c, hβ⟩]
      exact hval β ⟨c, hβ⟩ ⟨y.1, y.2⟩
    · have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
      rw [h0, show φ c y = 0 by rw [hram c (fun ⟨β, hβ⟩ => h ⟨β, hβ.symm⟩)]; rfl]
      have hz : KJInf.evalAt y.1 (0 : PY (I.rec7 l Z).what₂.Tau (B.R.N j)) = 0 := map_zero (MvPolynomial.eval _)
      rw [hz, zero_mul]
  have key := GlobalTheory.T.trueChainKernel_eq_classSum_jets I hOk hPins l Z u a Ch₀ A hP.is j hj1 hab φ Fc hFc a'.1 ⟨y'.1, y'.2⟩
  have e0 : (clsKL R g P r k tl s J A ι).val (j + 1) γ ((tupOf R P u g t r k tl).K j φ) a' y' = (I.chain l u a).K j φ a'.1 ⟨y'.1, y'.2⟩ := rfl
  rw [e0, key]
  letI := (I.chain l u a).clsFin j
  letI : Fintype ((tupOf R P u g t r k tl).Ch j) := (tupOf R P u g t r k tl).fin j
  rw [finsum_eq_sum_of_fintype]
  symm
  refine (Fintype.sum_sigma (fun x : (Σ β : (tupOf R P u g t r k tl).Ch j, (clsKL R g P r k tl s J A ι).cl j β) =>
      ((stabOrd (A.U j (ι j x.1)) (A.h j (ι j x.1) x.2) : ℕ) : ℂ)⁻¹ * A.abelian₂ j x.2.1 a'.1 (subY hab y'.1 (Fv x.1 x.2)) *
        ∏ τ, (y'.1 τ).det ^ (-(I.chain l u I.mu0).sDiv j τ))).symm.trans ?_
  refine Fintype.sum_of_injective (fun x => x.2.1) ?_ _ _ ?_ ?_
  · rintro ⟨β, c, hc⟩ ⟨β', c', hc'⟩ h
    simp only at h
    subst h
    have hb : β = β' := hinj (hc.symm.trans hc')
    subst hb
    rfl
  · intro c hc
    have h : ¬ ∃ β, A.chOf j c = ι j β := fun ⟨β, hβ⟩ => hc ⟨⟨β, c, hβ⟩, rfl⟩
    have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
    rw [h0]
    erw [map_zero (subY hab _), map_zero, mul_zero, zero_mul]
  · rintro ⟨β, c⟩
    have hst := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj.le (ι j β)).2.2 c
    simp only
    rw [hFcEq β c, hst]
    rfl

end GlobalTheory.AdForm.ClsKLive
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PlaceModelComb

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem mxAt_of_idemAt {es : AE D} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP) {Q : GlobalTheory.FinPl.Pl D → Prop}
    (hQ : Q ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) {m n : ℕ} {w : Mx D m n} (hw : IsHalf (es + cA D es) w) : GlobalTheory.FinPl.MxAt Q w := by
  obtain ⟨v, ε, hε, hsum⟩ := h.1.2.2
  obtain ⟨q, hqe, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v es ε h.1 hε hsum
  have hv : q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under q (hqe ▸ h)
  exact GlobalTheory.LevPin.mxAt_of_half q (hv ▸ hQ) w (hqe ▸ hw)

theorem mxAt_of_idemSum {e : AE D} {Pg : Finset (Pl D.host.E)} (hs : IsIdemSum e Pg) {m n : ℕ} {x : Mx D m n}
    (hx : IsHalf e x ∨ IsHalf (cA D e) x) :
    GlobalTheory.FinPl.MxAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hs
  intro i j
  rcases hx with hx | hx
  · rw [← hx i j, Finset.sum_mul]
    refine Ideal.sum_mem _ fun PP hPP => ?_
    have hw : IsHalf (es PP + cA D (es PP)) (es PP • x) := fun a b => by
      obtain ⟨h1, h2, -⟩ := (hes PP hPP).1
      rw [Matrix.smul_apply, smul_eq_mul, add_mul, ← mul_assoc, h1, ← mul_assoc, mul_comm (cA D (es PP)), h2,
        zero_mul, add_zero]
    have := mxAt_of_idemAt (Q := fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (hes PP hPP) ⟨PP, hPP, rfl⟩ hw i j
    rwa [Matrix.smul_apply, smul_eq_mul] at this
  · rw [← hx i j, map_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun PP hPP => ?_
    have hw : IsHalf (es PP + cA D (es PP)) (cA D (es PP) • x) := fun a b => by
      obtain ⟨h1, h2, -⟩ := (hes PP hPP).1
      rw [Matrix.smul_apply, smul_eq_mul, add_mul, ← mul_assoc, h2, zero_mul, zero_add, ← mul_assoc, ← map_mul, h1]
    have := mxAt_of_idemAt (Q := fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (hes PP hPP) ⟨PP, hPP, rfl⟩ hw i j
    rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (Pg : Finset (Pl D.host.E)) (P' : GlobalTheory.FinPl.Pl D → Prop), IsIdemSum e Pg → (∀ PP ∈ Pg, ¬ P' ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) → ∀ (d : WO S T →₀ ℂ), GlobalTheory.FinPl.CombAt P' d → ∀ (f₁ : WO S T → ℂ) (T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₁ T₁ → (∀ Φ, T₂ Φ = comb ψ S T d (T₁ Φ)) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (comb ψ S T d f₁) T₂ := by
  intro D ψ hψ S T Λ e Pg P' hs hd d hdc f₁ T₁ T₂ hT₁ hT₂
  have hd' : ∀ p, (∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → ¬ P' p := by
    rintro p ⟨PP, hPP, rfl⟩
    exact hd PP hPP
  have hcomm : ∀ x : WO S T, GlobalTheory.FinPl.MxAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x → ∀ f,
      heisO ψ S T x (comb ψ S T d f) = comb ψ S T d (heisO ψ S T x f) := by
    intro x hx f
    have h := (GlobalTheory.DisjComb.main D ψ hψ S T _ P' hd').1 (Finsupp.single x 1) d (fun u hu => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
      subst hu
      exact hx) hdc f
    simpa only [GlobalTheory.DisjComb.comb_single] using h
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [hT₂, hT₁.trans Φ hΦ x hx, ← hcomm x (mxAt_of_idemSum hs (Or.inl hx)), hT₂]
  · rw [hT₂, hT₁.modul Φ hΦ y hy, ← hcomm y (mxAt_of_idemSum hs (Or.inr hy)), hT₂]
  · rw [hT₂, hT₁.vac]

end GlobalTheory.PlaceModelComb
end
end
