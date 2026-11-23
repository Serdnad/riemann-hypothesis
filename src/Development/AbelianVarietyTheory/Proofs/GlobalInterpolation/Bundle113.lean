module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetIsometryEqOne
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.BarPass

variable {D : D7} {u : D.what₂.Word}

theorem valB_smul_eq {X : Ch D u} {i : ℕ} {M : PtModel X i} (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT)
    (g : M.G) (hg : ∀ v, M.loc v g = 1) (p : M.Pt) : Co.valB w V (g • p) = Co.valB w V p := by
  have h : ∀ v, (g • p).2 v = p.2 v := by
    intro v
    have h1 := M.smul_snd g p v
    rw [hg v] at h1
    apply Subtype.ext
    apply LocF.Raw.ext
    · ext x
      simpa using (h1 x).1
    · funext x
      simpa using (h1 x).2
  unfold PtModel.Coord.valB
  simp only [h]

variable {B : Built.Dat D u} {i : ℕ}

theorem ev_smul (c : D.what₂.LL) (F : B.V i) : B.ev i (c • F) = D.what₂.embLL c • B.ev i F :=
  LinearMap.map_smulₛₗ (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL) c F

theorem isIntegral_torsion {L : Type} [Field L] (ζ : CommGroup.torsion Lˣ) : IsIntegral ℤ ((ζ.1 : Lˣ) : L) := by
  obtain ⟨n, hn, h⟩ := (isOfFinOrder_iff_pow_eq_one).1 ((CommGroup.mem_torsion _).1 ζ.2)
  refine IsIntegral.of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h]
  exact isIntegral_one

theorem act_zeta_mem {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M) {Co : M.Coord}
    (hV : R.ValIs Co) {w : D.what₂.places.Pl} (hw : OverT B.ch w) (b) (d : (B.I.S i).D b) (ζ) (y : M.Val)
    (hy : y ∈ Co.valB w ∅ (R.pt b d)) : M.act (R.zeta ζ) y ∈ Co.valB w ∅ (R.pt b d) := by
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y).1 hy
  refine (hV.dual w hw b d _).2 ⟨((ζ.1 : (D.what₂.LL)ˣ) : D.what₂.LL) • F, ?_, ?_⟩
  · exact (B.valAt w i _).smul_mem (⟨_, isIntegral_torsion ζ⟩ : 𝓞 D.what₂.LL) hF
  · rw [R.act_zeta, ev_smul, ← hyF]
    rfl

theorem intBar_of_kerBar : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK _ _ hV hV' hb w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  rw [valB_smul_eq Co w ∅ _ (R.loc_zeta ζ)] at hy
  rw [valB_smul_eq Co' w ∅ _ (R'.loc_zeta ζ')]
  have hy0 := act_zeta_mem R hV hw b d ζ⁻¹ y hy
  have hyy : y = M.act (R.zeta ζ) (M.act (R.zeta ζ⁻¹) y) := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
  generalize M.act (R.zeta ζ⁻¹) y = y₀ at hy0 hyy
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y₀).1 hy0
  obtain ⟨F', hF', hk⟩ := hb w hw hs b b' d d' F hF
  have hm : B.ev (i + 1) F' ∈ M'.Val := by
    rw [R'.val_eq]
    exact evV_mem_ValC B.emb 1 _ D.what₂.embLL F'
  have h1 : (⟨_, hm⟩ : M'.Val) ∈ Co'.valB w ∅ (R'.pt b' d') := (hV'.dual w hw b' d' _).2 ⟨F', hF', rfl⟩
  refine ⟨_, act_zeta_mem R' hV' hw b' d' ζ' _ h1, ?_⟩
  rw [hyy, K.src, hT, ← map_smul]
  congr 1
  apply Subtype.ext
  rw [hK b b' d d' F y₀ hyF, hk, ev_smul, map_pow, map_natCast]
  rfl

end GlobalTheory.LvT.Built.BarPass
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section
namespace GlobalTheory.LvT.Built.DilPass

variable {D : D7} {u : D.what₂.Word}

theorem isAct_unique {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {p p₁ p₂ : LocF.PP Lc n}
    (h₁ : p.IsAct g p₁) (h₂ : p.IsAct g p₂) : p₁ = p₂ := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  apply Subtype.ext
  apply LocF.Raw.ext
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1]
  · funext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2]

theorem isDil_act {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {a : F}
    {p p' p₁ p₁' : LocF.PP Lc n} (h : LocF.PP.IsDil a p p') (h₁ : p.IsAct g p₁) (h₂ : p'.IsAct g p₁') :
    LocF.PP.IsDil a p₁ p₁' := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  refine ⟨?_, fun x => ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1, h.1]
  · obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2, h.2]

theorem dil_smul {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q : M.Pt} (h : M.Dil v a p q)
    (g : M.G) : M.Dil v a (g • p) (g • q) := by
  refine ⟨M.smul_fst g q p h.1, fun v' hv => ?_, isDil_act h.2.2 (M.smul_snd g p v) (M.smul_snd g q v)⟩
  have h1 := M.smul_snd g q v'
  rw [h.2.1 v' hv] at h1
  exact isAct_unique h1 (M.smul_snd g p v')

theorem dil_unique {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q q' : M.Pt} (h : M.Dil v a p q)
    (h' : M.Dil v a p q') : q = q' := by
  refine Prod.ext (h.1.trans h'.1.symm) (funext fun v' => ?_)
  by_cases hv : v' = v
  · subst hv
    apply Subtype.ext
    apply LocF.Raw.ext
    · rw [h.2.2.1, h'.2.2.1]
    · funext x
      rw [h.2.2.2, h'.2.2.2]
  · rw [h.2.1 v' hv, h'.2.1 v' hv]

theorem dil_pt {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    (v : B.ch.A.vT) (a : (B.ch.A.Fv v)ˣ) (b : (B.I.S i).β) (d : (B.I.S i).D b) :
    M.Dil v a (R.pt b d) (R.pt b ((B.J.A i).dia b (B.pr v) a d)) := by
  have hs : ∀ (P : B.ch.A.vT) (x : Fin (D.R.N i) → (M.Lc P).K), ∃ y : Fin (D.R.N i) → B.E, (fun c => R.iK P (y c)) = x :=
    fun P x => ⟨fun c => (R.iK P).symm (x c), funext fun c => by simp⟩
  have hL : ∀ P, ((R.pt b ((B.J.A i).dia b (B.pr v) a d)).2 P).1.L = ((R.pt b d).2 P).1.L := by
    intro P
    ext x
    obtain ⟨y, rfl⟩ := hs P x
    rw [R.pt_L, R.pt_L, (B.hJ.lev i).dia_N b (B.pr v) a d]
  refine ⟨?_, fun v' hv => ?_, hL v, fun x => ?_⟩
  · have h := (R.fst 1 b ((B.J.A i).dia b (B.pr v) a d) d).2
      ⟨1, map_one _, map_one _, by rw [one_smul]; exact (sp.off b).symm (sp.off_dia b d (B.pr v) a)⟩
    rwa [map_one, one_smul] at h
  · apply Subtype.ext
    apply LocF.Raw.ext (hL v')
    funext x
    obtain ⟨y, rfl⟩ := hs v' x
    exact (R.pt_f _ _ v' y).trans ((congrFun (sp.dia_deco b d (B.pr v) (B.pr v') a hv) y).trans (R.pt_f _ _ v' y).symm)
  · obtain ⟨y, rfl⟩ := hs v x
    refine (R.pt_f _ _ v y).trans (((B.hJ.lev i).dia_f b (B.pr v) a d y).trans ?_)
    rw [← R.pt_f b d v y]
    rfl

theorem ext_ev {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    {V : Type} [AddCommGroup V] [Module ℂ V] (φ ψ : M.Val →ₗ[ℂ] V)
    (h : ∀ F (y : M.Val), y.1 = B.ev i F → φ y = ψ y) : φ = ψ := by
  have hsp : M.Val = Submodule.span ℂ (Set.range (B.ev i)) := R.val_eq.trans (span_evV _ _ _ _).symm
  ext ⟨y, hy⟩
  have hy' : y ∈ Submodule.span ℂ (Set.range (B.ev i)) := hsp ▸ hy
  have key : ∀ y ∈ Submodule.span ℂ (Set.range (B.ev i)), ∀ hy : y ∈ M.Val, φ ⟨y, hy⟩ = ψ ⟨y, hy⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨F, rfl⟩ := hz
      exact fun hy => h F _ rfl
    | zero => exact fun hy => (map_zero φ).trans (map_zero ψ).symm
    | add a b ha hb iha ihb =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      have hb' : b ∈ M.Val := hsp ▸ hb
      exact (map_add φ ⟨a, ha'⟩ ⟨b, hb'⟩).trans ((congrArg₂ (· + ·) (iha ha') (ihb hb')).trans (map_add ψ ⟨a, ha'⟩ ⟨b, hb'⟩).symm)
    | smul r a ha iha =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      exact (map_smul φ r ⟨a, ha'⟩).trans ((congrArg (r • ·) (iha ha')).trans (map_smul ψ r ⟨a, ha'⟩).symm)
  exact key y hy' hy

theorem dilLaw_of_kerDil : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  intro D u B i sp sp' M M' R R' k K hT hI hD v a p q p' q' h h'
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  have hq := dil_unique M h (dil_smul M (dil_pt R v a b d) (R.zeta ζ))
  have hq' := dil_unique M' h' (dil_smul M' (dil_pt R' v a b' d') (R'.zeta ζ'))
  have h0 : K.k (R.pt b ((B.J.A i).dia b (B.pr v) a d)) (R'.pt b' ((B.J.A (i + 1)).dia b' (B.pr v) a d')) =
      K.k (R.pt b d) (R'.pt b' d') := by
    refine ext_ev R _ _ fun F y hy => Subtype.ext ?_
    rw [hI _ _ _ _ F y hy, hI _ _ _ _ F y hy, hD b b' d d' (B.pr v) a]
  have hs : ∀ y : M.Val, M.act (R.zeta ζ) (M.act (R.zeta ζ)⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hq, hq']
  refine LinearMap.ext fun y => ?_
  rw [← hs y, K.src, K.src, hT, hT, h0]

end GlobalTheory.LvT.Built.DilPass
end
end

section

noncomputable section

namespace GlobalTheory.LvT.Built

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem levelPrimeDatum_diamond_invariant {E : Type} [Field E] [NumberField E] [StarRing E] (K : Type) [Field K] {n n' : ℕ}
    {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (d' : DecoSet (E := E) (n := n') (ST := ST) (SG := SG')) (P : ST)
    (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) : phiT K (DecoSet.dia1 P a d).1 (DecoSet.dia1 P a d').1 = phiT K d.1 d'.1 := by
  funext x
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun Q => forall_congr' fun y => ?_
  refine imp_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [DecoSet.dia1, DecoSet.dia, Deco.dia]
  exact Units.mul_right_inj _

theorem decoratedLatticePoint_move_diamond {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco = DecoSet.dia1 P a p.1.1.deco ∧
      (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.fr = p.1.1.fr ∧ (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.2 = p.1.2 := by
  have h : p.mv (DecoSet.dia1 P a p.1.1.deco) =
      ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ := dif_pos ⟨p.1.1.2, p.2⟩
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

theorem kAt_dia : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → ∀ b b' d d' (P : Pr.vT u) a, kAt W Ch sel mu cst L A u i b b' ((tdatAt sel mu cst L Tp u i).dia b P a d) ((tdatAt sel mu cst L Tp u (i + 1)).dia b' P a d') = kAt W Ch sel mu cst L A u i b b' d d' := by
  intro X Pr R W Ch sel S mu cst L G m2 u i _ _ _ _ _ Tp A h b b' d d' P a
  obtain ⟨Ξ, -, -, -, -, h⟩ := h b b' d d'
  have key : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p (p.mv (DecoSet.dia1 P a p.1.1.deco)) := by
    intro j p
    obtain ⟨h1, h2, h3⟩ := decoratedLatticePoint_move_diamond p P a
    refine ⟨?_, ?_, h2.symm, h3.symm⟩
    · rw [h1]; exact fun _ _ => rfl
    · rw [h1]; rfl
  have h0 := h d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have h1 := h _ _ (key d) (key d')
  refine h1.trans (Eq.trans ?_ h0.symm)
  rw [(decoratedLatticePoint_move_diamond d P a).1, (decoratedLatticePoint_move_diamond d' P a).1]
  unfold GlobalTheory.KerT.term
  rw [levelPrimeDatum_diamond_invariant]
  rfl

end GlobalTheory.LvT.Built
end
end

section

noncomputable section

namespace GlobalTheory.LvT.Built.SplitPts

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem exists_ufGL {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : GL (Fin n) E)
    (h : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1) : ∃ g : UF E n, ufGL E n g = γ := by
  obtain ⟨e, rfl⟩ := (toGLm E n).surjective γ
  refine ⟨⟨e, fun x y => ?_⟩, rfl⟩
  rw [← toGLm_mulVec e x, ← toGLm_mulVec e y]
  show star ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ x) ⬝ᵥ ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem sameOff_gmap {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    {N N' : Submodule (𝓞 E) (Sp E n)} (g : Sp E n ≃ₗ[E] Sp E n) (h : SameOff ST N N') :
    SameOff ST (gmap g N) (gmap g N') := fun w hw => by
  ext x
  rw [mem_localization_gmap, mem_localization_gmap, h w hw]

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

variable (sel) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (i : ℕ)

def offSetoid : Setoid (PtAt R sel mu cst u i) where
  r := SameOffPt sel mu cst u
  iseqv :=
    ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      fun h => ⟨fun w hw => (h.1 w hw).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩,
      fun h h' => ⟨fun w hw => (h.1 w hw).trans (h'.1 w hw), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
        h.2.2.2.trans h'.2.2.2⟩⟩

theorem off_of_notMem (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (h : (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) :
    ∀ P ∈ Pr.vT u, w ≠ P ∧ w ≠ conjPrime₂ P := fun P hP => ne_of_T_notMem hPr u ⟨P, hP⟩ h

theorem ys_congr (hPr : Pr.Ok) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal)
    {N N' : Submodule (𝓞 X.E) (Sp X.E (R.N i))} (h : SameOff (Pr.vT u) N N') :
    (ysAt R sel mu cst i).ys N' = (ysAt R sel mu cst i).ys N := by
  classical
  have h1 : ∀ w : rowSG Pr sel mu, localization₂ w.1.asIdeal N' = localization₂ w.1.asIdeal N := fun w =>
    (h w.1 (off_of_notMem u hPr
      ((Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)))).symm
  unfold ysAt
  split_ifs
  · show ybSet sel mu cst N' = ybSet sel mu cst N
    simp only [ybSet, locLat, h1]
  · rfl

theorem exists_split : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)), ∃ sp : Split (tdatAt sel mu cst L Tp u i) (Pr.T u), ∀ b p q, (sp.off b).r p q ↔ SameOffPt sel mu cst u p q := by
  intro X Pr R _ Ch sel S mu cst L G m2 u i hX hPr hs hT _ Tp
  classical
  have hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal :=
    fun w hw => notMem_QE hs mu hw (hPr.T_prime u) hT
  have hM := moveHyp_of_ok hPr u
  have hQ' : ∀ (P : Pr.vT u) (w : QE sel (mu : Chr X.F X.E X.K)), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2)
  have hy := ysAt_off (R := R) sel mu cst hPr u hQ i
  refine ⟨{ off := fun _ => offSetoid sel mu cst u i
            off_act := ?_
            off_lat := fun _ _ _ h => h.1
            ext := ?_
            surj := ?_
            off_up := ?_
            off_dn := ?_
            off_dia := ?_
            dia_deco := ?_
            gam_surj := ?_
            T_mem := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).1
            T_nsq := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).2
            nonconj := fun P hP Q hQ => (hM ⟨P, hP⟩).st ⟨Q, hQ⟩ }, fun _ _ _ => Iff.rfl⟩
  · rintro b g p q ⟨h1, h2, h3, h4⟩
    refine ⟨sameOff_gmap g.1.1 h1, ?_, ?_, ?_⟩
    · funext w x
      show (g.2.1.1 w).1.mulVec (p.1.1.deco.1.be w (g.1.1.symm x)) = (g.2.1.1 w).1.mulVec (q.1.1.deco.1.be w (g.1.1.symm x))
      rw [h2]
    · funext w
      show g.1.1 * p.1.1.fr w * ((g.2.2.1 w)⁻¹).1 = g.1.1 * q.1.1.fr w * ((g.2.2.1 w)⁻¹).1
      rw [h3]
    · show (fun v => g.1.1 v) '' p.1.2 = (fun v => g.1.1 v) '' q.1.2
      rw [h4]
  · rintro b p q ⟨-, h2, h3, h4⟩ h
    have hN := congrArg Deco.N h
    have hf := congrArg Deco.f h
    exact PtY.ext' (Subtype.ext (Deco.ext hN hf h2)) h3 h4
  · intro b p e he h
    have hok := GlobalTheory.LvT.Pts.ok_of_agree p.1.1.deco.2 he
      fun w => h w.1 (off_of_notMem u hPr (T_notMem_vGs hPr u w))
    have hm := PtY.mv_spec p ⟨_, hok⟩ (fun w => (h w.1 (off_of_notMem u hPr (hQ w.1 w.2))).symm)
      (ys_congr sel mu cst u i hPr hQ h)
    have e1 := congrArg Subtype.val hm.1
    refine ⟨PtY.mv p ⟨_, hok⟩, ⟨?_, (congrArg Deco.be e1).symm, hm.2.1.symm, hm.2.2.symm⟩, ?_⟩
    · rw [e1]; exact h
    · have hN := congrArg Deco.N e1
      have hf := congrArg Deco.f e1
      exact Deco.ext hN hf (funext fun w => absurd w.2 (Finset.notMem_empty _))
  · intro b p P x hx hf
    have hm := mv_up (Pr.T u) p P (hM P) (T_unif hX hPr u P) (hQ' P) (hy P) hx hf
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((upN_spec p.1.1.deco.2.lat p.1.1.deco.2.uni P.1 (hM P).ne hx).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P g hg
    have e : (tdatAt sel mu cst L Tp u i).deco b p = p.1.1.deco.1.res (Finset.empty_subset _) :=
      Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))
    rw [e] at hg
    have hg' := dn_ok_of_res p.1.1.deco.2 P (hM P) (g := g) hg
    have hm := mv_dn p P (hM P) (hQ' P) (hy P) hg'
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((p.1.1.deco.2.dnN_spec P (hM P).ne).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P a
    show SameOffPt sel mu cst u p (PtY.mv p (DecoSet.dia1 P a p.1.1.deco))
    rw [PtY.mv_dia]
    exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  · intro b p P P' a hne
    show (PtY.mv p (DecoSet.dia1 P a p.1.1.deco)).1.1.deco.1.f P' = p.1.1.deco.1.f P'
    rw [PtY.mv_dia]
    funext x
    show ((Pi.mulSingle P a : DiaG (E := X.E) (ST := Pr.vT u)) P').1 * _ = _
    rw [Pi.mulSingle_eq_of_ne hne, Units.val_one, one_mul]
  · intro b γ h
    obtain ⟨g, hg⟩ := exists_ufGL γ h
    exact ⟨(g, 1, 1), hg⟩

end GlobalTheory.LvT.Built.SplitPts
end
end

section

noncomputable section

namespace GlobalTheory.LvT.Built.IntPPass

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem ev_smul {D : D7} {u : D.what₂.Word} (B : Built.Dat D u) (i : ℕ) (c : D.what₂.LL) (F : B.V i) :
    B.ev i (c • F) = D.what₂.embLL c • B.ev i F := by
  unfold Built.Dat.ev
  exact map_smulₛₗ _ _ _

theorem intP_of_kerP : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerP k → K.IntP Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK hCo hCo' hV hV' hP w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  set g := R.zeta ζ with hg
  set g' := R'.zeta ζ' with hg'
  have h0 := (GlobalTheory.LvT.ValEq.valB_laws D u B.ch i M Co hCo w hw ∅ (g • R.pt b d)).2.2.2 g⁻¹ y hy
  rw [inv_smul_smul] at h0
  set y₀ := M.act g⁻¹ y with hy₀
  have hyy : y = M.act g y₀ := by
    rw [hy₀, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨F, hF, hFy⟩ := (hV.dual w hw b d y₀).1 h0
  have h1 := hP w hw hs b b' d d' F hF
  have h2 := hK b b' d d' F y₀ hFy
  rw [hT, hyy, K.src, ← map_smul]
  refine (GlobalTheory.LvT.ValEq.valB_laws D u B.ch (i + 1) M' Co' hCo' w hw Finset.univ (R'.pt b' d')).2.2.2 g' _ ?_
  refine (hV'.ker w hw hs b' d' _).2 ⟨_, h1, ?_⟩
  rw [ev_smul, ← h2, map_zpow₀, map_natCast]
  rfl

end GlobalTheory.LvT.Built.IntPPass
end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.norm_kappa_sq_mul_det_isometry_eq_one : ∀ (D : D7) (γ₀ γ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → γ.AtP q → ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  first | exact @GlobalTheory.KapVal.norm_kappa_sq_mul_det | exact GlobalTheory.KapVal.norm_kappa_sq_mul_det | (intros; apply GlobalTheory.KapVal.norm_kappa_sq_mul_det <;> assumption)
end
