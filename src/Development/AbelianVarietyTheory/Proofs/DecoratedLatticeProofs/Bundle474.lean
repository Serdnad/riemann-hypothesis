module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle418
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle460
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle459
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalFramePlaceYZeroPrimitiveInHomLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulColMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle445
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.StabPair

open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec_any (p : SplitPt D k) {S : HSp D} (h : GA D S) (y : Fin S.rank → k) :
    Formalism.L2.Theta.mt S h *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((((Formalism.L2.Theta.mt S h).map p.pr) *ᵥ y) i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]

theorem col_mulVec {m : Type} [Fintype m] (Y : m → k) (t : Fin 1 → k) :
    Matrix.replicateCol (Fin 1) Y *ᵥ t = t 0 • Y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.replicateCol, mul_comm]

theorem vec_emb {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀)
    (g : GL n k) (x : n ⊕ Fin 1 → k) :
    (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (β₀.b *ᵥ x) =
      β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr) := by
  have hA : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jA.map p.pr = o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [← Matrix.map_mul, o.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jB.map p.pr = o.jB.map p.pr := by
    rw [← Matrix.map_mul, o.emb_jB]
    simp
  have hz : (fun i => p.pr (ratV (vecB o ζ) i)) = o.jB.map p.pr *ᵥ (fun j => p.pr (incA D (ζ j))) := by
    funext i
    simp [ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat]
  have hY : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) =
      (fun i => p.pr (ratV (vecB o ζ) i)) := by
    rw [hz, Matrix.mulVec_mulVec, hB]
  rw [hs, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec, col_mulVec, col_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hY,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA]
  have e : o.jA.map p.pr * (β.b * g.val * β.b') * β.b = (o.jA.map p.pr * β.b) * g.val := by
    simp only [Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem mem_glued_iff {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} {M : Lat S} {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (hG : GluedW β₀ M q m P) (x : n ⊕ Fin 1 → k) :
    (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
      ∃ s : 𝒪[k], x ∘ Sum.inl - s • P.vec ∈ P.ker ∧ m * x (Sum.inr 0) = q.inv * s := by
  rw [hG x, GlobalTheory.LevelUnfold.mem_gluedS, Sum.elim_comp_inl]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  simp [Fin.forall_fin_one]

theorem glued_stab {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    {g : GL n k} (hP : g • P = P) {u : n → k} {t : k}
    (h : ∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) :
    ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := by
  obtain ⟨hk, hv⟩ := (GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec).1 hP
  obtain ⟨s, h1, h2⟩ := h
  refine ⟨s, ?_, h2⟩
  have h3 : g • (u - s • P.vec) ∈ P.ker := hk ▸ Submodule.smul_mem_pointwise_smul _ g _ h1
  have e : g.val *ᵥ u - s • P.vec = g • (u - s • P.vec) + s • (g • P.vec - P.vec) := by
    rw [smul_sub, smul_sub, smul_comm g s]
    change _ = g • u - _ + _
    change _ = g.val *ᵥ u - _ + _
    abel
  rw [e]
  exact add_mem h3 (P.ker.smul_mem s hv)

theorem glued_zero {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (u : n → k) : (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * 0 = q.inv * s) ↔ u ∈ P.ker := by
  constructor
  · rintro ⟨s, h1, h2⟩
    have hs : (s : k) = 0 := by
      rw [mul_zero, eq_comm, mul_eq_zero] at h2
      exact h2.resolve_left (inv_ne_zero q.ne_zero)
    have hs' : s = 0 := Subtype.ext hs
    simpa [hs'] using h1
  · intro h
    exact ⟨0, by simpa using h, by simp⟩

end GlobalTheory.Core.Mi.LatMatch.StabPair


open GlobalTheory.Core.Mi.LatMatch.StabPair in
theorem GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n), IsSumFrame o ζ β β₀ → IsSelfDualC S M → m ≠ 0 → GluedW β₀ M q m P → ∀ g : GL n k, Moves S (o.emb (β.gl g, 1)) M M (· = p.v) ↔ g • P = P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M q m P hs hM hm hG g
  have hE : ∀ x : n ⊕ Fin 1 → k, Formalism.L2.Theta.mt S (o.emb (β.gl g, 1)) *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) =
      fun i => p.sec ((β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr)) i) := fun x => by
    rw [mt_sec_any, vec_emb o ζ hs]
  constructor
  · intro hmov
    have hGG : ∀ (u : n → k) (t : k), (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) ↔
        ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := fun u t => by
      have := hmov (fun i => p.sec ((β₀.b *ᵥ Sum.elim u fun _ => t) i)) (fun i => GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _)
      rw [hE, mem_glued_iff hG, mem_glued_iff hG] at this
      simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Function.comp_apply] using this
    rw [GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec]
    have hker : ∀ u, u ∈ P.ker ↔ g.val *ᵥ u ∈ P.ker := fun u => by
      rw [← glued_zero (q := q) (m := m), ← glued_zero (q := q) (m := m), hGG]
    refine ⟨?_, ?_⟩
    · ext y
      rw [GlobalTheory.LatPair.mem_smul_iff, hker]
      change g.val *ᵥ ((g⁻¹ : GL n k).val *ᵥ y) ∈ P.ker ↔ _
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    · have h1 : ∃ s : 𝒪[k], P.vec - s • P.vec ∈ P.ker ∧ m * (m⁻¹ * q.inv) = q.inv * s :=
        ⟨1, by simp, by rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]; simp⟩
      obtain ⟨s, h2, h3⟩ := (hGG _ _).1 h1
      have hq : q.inv ≠ 0 := inv_ne_zero q.ne_zero
      have hs : (s : k) = 1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul] at h3
        exact mul_left_cancel₀ hq (h3.symm.trans (mul_one _).symm)
      have hs' : s = 1 := Subtype.ext hs
      change g.val *ᵥ P.vec - P.vec ∈ P.ker
      simpa [hs'] using h2
  · intro hP
    refine (sMoves_one _ _ _ _).1 (GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S M M 1 _ hM hM (normOneAt_one _) fun x => ?_)
    rw [map_one, one_smul]
    obtain ⟨y, rfl⟩ : ∃ y, x = β₀.b *ᵥ y := ⟨β₀.b' *ᵥ x, by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]⟩
    rw [vec_emb o ζ hs, mem_glued_iff hG, mem_glued_iff hG]
    simp only [Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply]
    refine ⟨glued_stab hP, fun h => ?_⟩
    have := glued_stab (inv_smul_eq_iff.2 hP.symm) h
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastPeriod_tail_eq_lowered_evaluation_period : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → (∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c)) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ f : CXP R P t, (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * ∑ β ∈ @Finset.univ (k.Ch n) (k.fin n), ∑ c : (I.fm l u a).clsP, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f ((realOf u R g s J).low n hn fun z => k.rd n β ψ (((realOf u R g s J).fr n).symm z) ((g.oT n hn).emb (h c, 1))) = k.cP * (tupOf R P u g t r k tl).tail n hn ψ f := by
  first | exact @GlobalTheory.AdForm.tailTop_eq_of_pin | exact GlobalTheory.AdForm.tailTop_eq_of_pin | (intros; apply GlobalTheory.AdForm.tailTop_eq_of_pin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_measure_value : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ PP, QAll W PP → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.tP := by
  first | exact @GlobalTheory.tuplePlace_under_not_mem_tP | exact GlobalTheory.tuplePlace_under_not_mem_tP | (intros; apply GlobalTheory.tuplePlace_under_not_mem_tP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_measure_scalar : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.FinPl.AdaptFB (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).J j (σ + 1) h) ((commOf (pk W) u (mkGeo m b₀)).B (j + 1 + 1) σ (idx_step h)) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L (N₁ (j + 1 + 1)) (M₁ (j + 1 + 1) σ (idx_step h)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.Fam.adaptFB_of_normalFrames | exact GlobalTheory.Fam.adaptFB_of_normalFrames | (intros; apply GlobalTheory.Fam.adaptFB_of_normalFrames <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_measure_relation : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ j ρ h, ∃ L : GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀, IsSelfDualC (y.bes j ρ h).V₀ L := by
  first | exact @GlobalTheory.CoreLat.exists_selfDual_core | exact GlobalTheory.CoreLat.exists_selfDual_core | (intros; apply GlobalTheory.CoreLat.exists_selfDual_core <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierJacobiLattice_splits_at_normalFrame_place : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.jac j ρ h).lev (a.x (j + 1)).vol).d (N (j + 1)) (a.x (j + 1)).L ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.Fam.monoW_of_normalFrames | exact GlobalTheory.Fam.monoW_of_normalFrames | (intros; apply GlobalTheory.Fam.monoW_of_normalFrames <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselToJacobiMap_carries_normalFrameLines : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.ColsAt ((y.bes j ρ h).lev (a.x j).vol).d (xZero ((y.jac j ρ h).lev (a.x (j + 1)).vol).d) (N j) (N (j + 1)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.ColsXZeroNormal.colsAt_xZero_of_normalFr | exact GlobalTheory.ColsXZeroNormal.colsAt_xZero_of_normalFr | (intros; apply GlobalTheory.ColsXZeroNormal.colsAt_xZero_of_normalFr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_normalFrames_rationalDecompositions_over_local : ∀ {D : D7} (a : XGeo D) (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (n : ℕ), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E) → ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∃ (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc := by
  first | exact @GlobalTheory.Fam.FramesY.normalFrames_exist | exact GlobalTheory.Fam.FramesY.normalFrames_exist | (intros; apply GlobalTheory.Fam.FramesY.normalFrames_exist <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.normalFrame_place_yZero_primitive_in_hom_lattice : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), 0 < ρ → ∀ t ∈ GlobalTheory.FinPl.idAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.incAdj ((y.bes j ρ h).lev (a.x j).vol).V₀ (t • yZero ((y.bes j ρ h).lev (a.x j).vol).V₀ ρ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ)) ∈ latO ((y.bes j ρ h).lev (a.x j).vol).V₀ ((y.jac j ρ h).lev (a.x (j + 1)).vol).W (M j ρ h : Set _) (N (j + 1) : Set _) (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ↔ t ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) := by
  first | exact @GlobalTheory.SplitLastPt.normalFr_incAdj_yZero_mem_latO_iff | exact GlobalTheory.SplitLastPt.normalFr_incAdj_yZero_mem_latO_iff | (intros; apply GlobalTheory.SplitLastPt.normalFr_incAdj_yZero_mem_latO_iff <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.GoodPos

variable {D : D7}

theorem incAdj_yZero_mulVec {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (z : Fin V₀.rank → D.host.E) (a : AE D) (y : Fin V₀.rank → AE D) :
    (show Matrix (Fin W.rank) (Fin V₀.rank) (AE D) from d.incAdj V₀ (a • yZero V₀ ρ z)) *ᵥ y =
      colMul d.jY r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
  have h1 : (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀)) *ᵥ y =
      Pi.single r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
    rw [smul_mulVec, ← mulVec_mulVec, herm_eq]
    generalize gA V₀ *ᵥ y = t
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, adj, yZero, zEll, ell, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, RingHom.map_neg]
    by_cases hi : i = r
    · subst hi
      simp only [hr, if_true, mul_one, Pi.single_eq_same, mul_neg, RingHom.map_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    · have : ¬ (i.1 + 1 = ρ) := fun h => hi (Fin.ext (by omega))
      simp only [this, if_false, mul_zero, neg_zero, RingHom.map_zero, zero_mul, Finset.sum_const_zero, Pi.single_eq_of_ne hi]
  change (d.jY ⬝ (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀))) *ᵥ y = _
  rw [← mulVec_mulVec, h1, mulVec_single]
  funext k
  exact mul_comm _ _

theorem mxAt_mul {P : Pl D → Prop} {l m n : ℕ} (M : Mx D l m) {N : Mx D m n} (h : MxAt P N) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k j)

theorem mxAt_mul' {P : Pl D → Prop} {l m n : ℕ} {M : Mx D l m} (N : Mx D m n) (h : MxAt P M) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (a : AE D) {N : Mx D m n} (h : MxAt P N) : MxAt P (a • N) := fun i j =>
  Ideal.mul_mem_left _ _ (h i j)

theorem mxAt_adj {x : Pl D} {m n : ℕ} {N : Mx D m n} (h : MxAt (· = x) N) : MxAt (· = x) (adj N) := fun i j =>
  id_conj (h j i)

def xiU (D : D7) : (AE D)ˣ := inU D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem cA_xi : cA D (incA D D.host.xi0) = -incA D D.host.xi0 := by
  rw [FrameLat.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg]

theorem cA_xi_inv : cA D (incA D D.host.xi0⁻¹) = -incA D D.host.xi0⁻¹ := by
  rw [FrameLat.cA_incA, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, RingHom.map_neg]

theorem last_of {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} {LW : Lat W}
    (hM : IsSelfDualC V₀ M) (hLW : IsSelfDualC W LW) {x : Pl D} {α m : (AE D)ˣ} {b : Fin ρ → (AE D)ˣ}
    (hb : ∀ r : Fin ρ, r.1 + 1 = ρ → b r = xiU D * cU α * m)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hW : ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV W LW (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hρ : 0 < ρ) : ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D V₀ M x hM
  have hr : (⟨ρ - 1, by omega⟩ : Fin ρ).1 + 1 = ρ := by simp only; omega
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [LatMem.mem_latO_iff D V₀ W M LW hM hLW, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hα, smul_colMul, hW _ _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (LocSD.hermAt_mem_idAt (hsd.1 y hy) _))), hb _ hr, ← int_neg,
    ← herm_conj V₀ y, int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1, Units.val_mul, Units.val_mul, RingHom.map_mul, RingHom.map_mul, cU_val, Formalism.L2.Theta.cA_cA, xiU, inU_val, cA_xi]
  have e2 := α.mul_inv
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D D.host.xi0 * incA D D.host.xi0⁻¹ * cA D m * hermAt V₀ y (a • ratV z)) * e2 +
    (cA D m * hermAt V₀ y (a • ratV z)) * e3

theorem herm_kap {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (w : WO S L'') (l : Fin L.rank → AE D)
    (s : Fin S.rank → AE D) :
    hermAt S ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ l) s =
      incA D (-D.host.xi0⁻¹) * hermAt L l ((rat τ : Mx D _ _) *ᵥ ((show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s)) := by
  rw [mulVec_mulVec]
  change hermAt S ((incA D (-D.host.xi0⁻¹) • (giA S ⬝ (adj (rat τ ⬝ w) ⬝ gA L))) *ᵥ l) s = _
  generalize ((rat τ : Mx D _ _) ⬝ w : Mx D L.rank S.rank) = u
  rw [herm_eq, herm_eq, mulVec_mulVec, Matrix.mul_smul, gA_giA_cancel, smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← mulVec_mulVec, dotProduct_mulVec]
  congr 2
  ext i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, adj, map_sum, map_mul, mul_comm]

theorem kap_of {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} (hζ : IsLineVec L ζ) (hζ₀ : IsLineVec L'' ζ₀) {lam : D.host.E} (hlam : lam ≠ 0)
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α μ : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ ((μ⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hm : ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔
      (((α * μ * inU lam hlam * (xiU D * cU α)⁻¹)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x) := by
  intro w hw
  rw [LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ] at hw
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  have hmx : MxAt (· = x) (kap τ S w) := mxAt_smul _ (mxAt_mul _ (mxAt_mul' _ (mxAt_adj (mxAt_mul _ hw.1))))
  rw [LatMem.mem_latO_iff D L S LL LS hLL hLS]
  refine ⟨hmx, fun l hl => ?_⟩
  have hn := line_norm hζ hLL hm
  obtain ⟨a, ha, rfl⟩ := line_vec hζ (latV_idAt hl)
  rw [hα]
  refine (hsd.2.2 _ ?_).2 ?_
  · exact fun i => Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (latV_idAt hl) i)
  intro s hs
  have h1 := (hα _ _ _).1 (hw.2 s hs)
  obtain ⟨a', ha', e'⟩ := line_vec hζ₀ (latV_idAt h1)
  rw [e'] at h1
  have e2 : (show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s = ((α : AE D) * a') • ratV ζ₀ := by
    rw [mul_smul, ← e', smul_smul, Units.mul_inv, one_smul]
  have e1 := herm_smul S ((α⁻¹ : (AE D)ˣ) : AE D) 1 ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ a • ratV ζ) s
  rw [one_smul] at e1
  rw [e1, herm_kap, e2, mulVec_smul, rat_mulVec, hτ, ratV_smul, smul_smul, herm_smul, herm_rat]
  have h2 := int_mul ((hm a ha).1 hl) (int_conj.2 ((hμ a' ha').1 h1))
  rw [hn _ h2.1] at h2
  convert h2 using 1
  generalize hm' : α * μ * inU lam hlam * (xiU D * cU α)⁻¹ = m
  have f1 := m.mul_inv
  have f2 : cA D (μ : AE D) * cA D ((μ⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU μ).mul_inv
  have f3 : cA D (m : AE D) = cA D α * cA D μ * cA D (incA D lam) * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) := by
    rw [← hm', mul_inv]
    simp only [Units.val_mul, RingHom.map_mul, inU_val, cU_inv, Formalism.L2.Theta.cA_cA, xiU, inU_inv, cA_xi_inv]
  rw [f3]
  simp only [RingHom.map_mul, RingHom.map_neg, RingHom.map_one]
  generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = h
  linear_combination (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a') * f2 +
    (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a' * (cA D μ * cA D (μ⁻¹ : (AE D)ˣ))) * f1

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}

theorem isU_xi (h : p.UnitAA) : IsU p.v (xiU D : AE D) :=
  IsU.of_pres (xiU D).mul_inv (fun a ha => (h.1 a ha).1) fun a ha => (h.1 a ha).2

theorem isU_alpha (h : p.UnitAA) {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = p.v) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = p.v)) :
    IsU p.v (α : AE D) := by
  have hgen : ∃ e : D.host.E, e ≠ 0 ∧ ∀ a ∈ idAt D (· = p.v),
      a • ratV ζ ∈ latV L (GlobalTheory.AdelicU.frameLat L) (· = p.v) ↔
        incA D e⁻¹ * a ∈ intAt D (· = p.v) := by
    first
    | exact GlobalTheory.GoodPos.line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L) p.v
    | exact GlobalTheory.GoodPos.line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1 p.v
  obtain ⟨e, he, hg⟩ := hgen
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h.2, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

theorem val_le_one {u : AE D} (h : IsU p.v u) : valuation k (p.pr u) ≤ 1 := by
  refine (p.int_iff _).2 ?_
  rw [p.sec_pr, mul_comm]
  exact ((h _ (FrameLat.e_mem_idAt p)).1 (FrameLat.e_mem_intAt p)).2

theorem val_eq_one {u : (AE D)ˣ} (h : IsU p.v (u : AE D)) : valuation k (p.pr u) = 1 := by
  have h1 := val_le_one h
  have h2 := val_le_one (h.inv u.mul_inv)
  have h3 : valuation k (p.pr u) * valuation k (p.pr (u⁻¹ : (AE D)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  exact le_antisymm h1 (by rw [← h3]; exact mul_le_of_le_one_right' h2)

end Split

end GlobalTheory.GoodPos

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeVacuum_heckeIdentity_splitPlace_charts : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ eS eT, IsSplitChart D.sp.cm.sig S.gram (frameLat S) h eS → IsSplitChart D.sp.cm.sig T.gram (frameLat T) h eT → ∀ f, VacFin ψ S T v f → (∀ k ∈ Kv S v, ∀ k' ∈ Kv T v, om (embV S v k, embV T v k') f = f) ∧ ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ k ≤ T.rank, heckeVec (((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom) (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f = ∑ j ∈ Finset.range (S.rank + 1), (if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) * (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k * (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0) • heckeVec (((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom) (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
  first | exact @GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart | exact GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart | (intros; apply GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart <;> assumption)
end
