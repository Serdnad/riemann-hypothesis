module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle003
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Gen
variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (h : s * s = Δ) (h' : s' * s' = Δ) (e : s = s') :
    Sig.eD h = Sig.eD h' := by
  subst e; rfl

private theorem mem_lvS (A : SD Δ) (y : DA Δ) (g : SA Δ) :
    g ∈ A.lvS y ↔ y⁻¹ * (g : DA Δ) * y ∈ A.dat.U2 := by
  unfold SD.lvS
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  show (MulAut.conj y⁻¹) (g : DA Δ) ∈ _ ↔ _
  rw [MulAut.conj_apply, inv_inv]

private theorem conj_at (y g : DA Δ) (v : Pl F) (h : y.1 v = 1) : (y⁻¹ * g * y).1 v = g.1 v := by
  have : (y⁻¹ * g * y).1 v = (y.1 v)⁻¹ * g.1 v * y.1 v := rfl
  rw [this, h, inv_one, one_mul, mul_one]

private theorem up (A A₀ : SD Δ) (hA : A.Ok) (hA₀ : A₀.Ok) (hE : A.Ext A₀) (x : DA Δ) (h0 : x ∈ A₀.dat.U2)
    (hn : ∀ v (h : v ∈ A.Sg), v ∉ A₀.Sg → Sig.eD (A.hs v h) (x.1 v) ∈ (Sig.Lev.iw (Kv v)).J 2) : x ∈ A.dat.U2 := by
  have d0 := ((datOk F Δ A₀ hA₀).2.2.2.2 x).1 h0
  refine ((datOk F Δ A hA).2.2.2.2 x).2 ⟨fun v hv => ?_, fun v hv => d0.2 v fun h => hv (hE.sub h)⟩
  by_cases h : v ∈ A₀.Sg
  · rw [hE.V v h, eD_congr (A.hs v hv) (A₀.hs v h) (hE.s v h)]
    exact d0.1 v h
  · rw [hE.iw v hv h]
    exact hn v hv h

end Gen

section Br
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L}

private theorem spl (hB : B.Ok) (w : Plc L) (R : B.toRingBr.Split w) (g : SA B.Δ)
    (h : cLoc w (B.bS g : UA L 2) ∈ (iw w).J 2) :
    Sig.eD R.hs ((g : DA B.Δ).1 (un w)) ∈ (Sig.Lev.iw (Kv (un w))).J 2 := by
  rw [hB.splS w R g] at h
  exact (R.J (Sig.Lev.iw _) (iw w) rfl (fun a => R.Uo a) 2 _).1 h

private theorem lev_mem {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)} {V : ∀ w : Plc L, Sig.Lev (Kw w)} {x : UA L n}
    (h : x ∈ lev U S V) : x ∈ U ∧ ∀ w ∈ S, cLoc w x ∈ (V w).J n := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
  refine ⟨h1, fun w hw => ?_⟩
  simp only [Subgroup.mem_iInf] at h2
  exact h2 w hw

end Br


theorem UpperTheory.V.Z.Sym.So.levExt :
    UpperTheory.V.Z.Sym.So.LevExt := by
  intro L _ _ _ B hB T S VL A hA hF A₀ hA₀ hE S₁ h1 _ U y hy hU g hg
  obtain ⟨hgU, hgJ⟩ := lev_mem hg
  refine (mem_lvS A y g).2 (up A A₀ hA hA₀ hE _ ((mem_lvS A₀ y g).1 (hU g hgU)) ?_)
  intro v hv h0
  obtain ⟨w, hwS, rfl⟩ := (hF.sg v).1 hv
  have hsp : IsSplitAt w := hF.pl.split w hwS
  rw [conj_at y (g : DA B.Δ) _ (hy _ hv), eD_congr (A.hs _ hv) (T w hsp).hs (hF.s w hwS hsp)]
  exact spl hB w (T w hsp) g (hgJ w ((h1 w hwS).resolve_right h0))

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trim {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (y : DA Δ) (hy : D.Off y) :
    ∃ t w : DA Δ, w ∈ D.U2 ∧ t * w = y ∧ D.Off t ∧ {v | t.1 v ≠ 1}.Finite := by
  classical
  let P : Pl F → Prop := fun v => y.1 v ∈ KD ((cv v) Δ) (Ov v) ∧ v ∉ D.Sg
  have hfin : {v | y.1 v ∉ KD ((cv v) Δ) (Ov v)}.Finite := Filter.eventually_cofinite.mp y.2
  have hbad : {v | ¬ P v}.Finite := by
    refine (hfin.union D.Sg.finite_toSet).subset ?_
    intro v hv
    by_cases h1 : y.1 v ∈ KD ((cv v) Δ) (Ov v)
    · exact Or.inr (by_contra fun h2 => hv ⟨h1, h2⟩)
    · exact Or.inl h1
  refine ⟨⟨fun v => if P v then 1 else y.1 v, ?_⟩, ⟨fun v => if P v then y.1 v else 1, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine Filter.eventually_cofinite.mpr (hbad.subset ?_)
    intro v hv h
    apply hv
    show (if P v then 1 else y.1 v) ∈ KD ((cv v) Δ) (Ov v)
    rw [if_pos h]
    exact one_mem _
  · show ∀ᶠ v in Filter.cofinite, (if P v then y.1 v else 1) ∈ KD ((cv v) Δ) (Ov v)
    refine Filter.Eventually.of_forall fun v => ?_
    by_cases h : P v
    · rw [if_pos h]
      exact h.1
    · rw [if_neg h]
      exact one_mem _
  · simp only [Dat.U2, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show (if P v then y.1 v else 1) ∈ D.J2v v
    by_cases h : P v
    · rw [if_pos h, Dat.J2v, if_neg h.2]
      exact h.1
    · rw [if_neg h]
      exact one_mem _
  · refine Subtype.ext (funext fun v => ?_)
    show (if P v then 1 else y.1 v) * (if P v then y.1 v else 1) = y.1 v
    split_ifs <;> simp
  · intro v hv
    show (if P v then 1 else y.1 v) = 1
    split_ifs
    · rfl
    · exact hy v hv
  · refine hbad.subset ?_
    intro v hv h
    apply hv
    show (if P v then 1 else y.1 v) = 1
    rw [if_pos h]

theorem UpperTheory.V.Z.Sym.So.repsEx :
    UpperTheory.V.Z.Sym.So.RepsEx := by
  intro F _ _ Δ A hA hCR ι hι
  classical
  obtain ⟨Y, hY, hdec⟩ := hCR F Δ A.dat (datOk F Δ A hA).1 ι hι
  let f : DA Δ → DA Δ := fun y => if h : A.dat.Off y then (trim A.dat y h).choose else y
  refine ⟨Y.image f, ?_, ?_⟩
  · intro y' hy'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
    obtain ⟨w, -, -, ht, hfin⟩ := (trim A.dat y (hY y hy)).choose_spec
    simp only [f, dif_pos (hY y hy)]
    exact ⟨ht, hfin⟩
  · intro g
    obtain ⟨γ, s, hs, y, hy, u, hu, rfl⟩ := hdec g
    obtain ⟨w, hw, hty, -, -⟩ := (trim A.dat y (hY y hy)).choose_spec
    refine ⟨γ, s, hs, f y, Finset.mem_image_of_mem f hy, w * u, mul_mem hw hu, ?_⟩
    simp only [f, dif_pos (hY y hy)]
    conv_lhs => rw [← hty]
    simp only [mul_assoc]

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem uf_dg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (V : Lev k) (d d' : Fin 2 → kˣ) (hd : Dom d) (hd' : Dom d') : UF (V.J 2) (dg d) (dg d') := by
  intro g
  have h := dCMul k V 2 d d' hd hd' g
  have hm : dg (d * d') = dg d * dg d' := map_mul _ _ _
  simp only [Lev.DC, hm] at h
  exact h

theorem UpperTheory.V.Z.Sym.So.dMul :
    UpperTheory.V.Z.Sym.So.DMul := by
  intro F _ _ Δ A hA g d hg
  classical
  let P := rpg (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v))
  have hpv : ∀ (x : DA Δ) v, P.p v x = (x : (v : Pl F) → ↥(DX ((cv v) Δ))) v := fun _ _ => rfl
  have hU : ∀ v ∉ A.Sg, A.dat.J2v v = KD ((cv v) Δ) (Ov v) := by
    intro v hv
    simp [Dat.J2v, SD.dat, hv]
  have hJ : ∀ v (hv : v ∈ A.Sg),
      A.dat.J2v v = Subgroup.comap (eD (A.hs v hv)) ((A.V v).J 2) := by
    intro v hv
    simp [Dat.J2v, SD.dat, hv, Lev.data]
  have hok := datOk F Δ A hA
  have hout : ∀ (x : DA Δ) (e : ParN F 2), A.IsElD x e → ∀ v ∉ A.Sg, P.p v x ∈ A.dat.J2v v := by
    intro x e hx v hv
    rw [hU v hv, hpv, hx.2 v hv]
    exact one_mem _
  have hbox := uFBox (Pl F) (DA Δ) (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v))
    A.dat.J2v P A.Sg hU g (hout g d hg)
  have key : ∀ v (hv : v ∈ A.Sg),
      UpperTheory.V.AlgebraTools.FinOrb (A.dat.J2v v) (A.dat.J2v v) (P.p v g) ∧
      ∀ (g' : DA Δ) (d' : ParN F 2), A.IsElD g' d' → Dom (d v) → Dom (d' v) →
        UF (A.dat.J2v v) (P.p v g) (P.p v g') := by
    intro v hv
    obtain ⟨hI, h2, hs0, -, -⟩ := hok.2.2.1 v hv
    have hb := (eD_facts (Kv v) (Ov v) hI h2 ((cv v) Δ) (A.s v) (A.hs v hv) hs0).1
    rw [hJ v hv]
    constructor
    · have dm := dcMap _ _ ℂ (eD (A.hs v hv)) hb ((A.V v).J 2) (P.p v g) (P.p v g)
      rw [dm.2.1, hpv, hg.1 v hv]
      exact ((finFacts (Kv v) (A.V v)).2.2.2.2.2 2).1 _
    · intro g' d' hg' hd hd'
      have dm := dcMap _ _ ℂ (eD (A.hs v hv)) hb ((A.V v).J 2) (P.p v g) (P.p v g')
      rw [dm.2.2.1, hpv, hpv, hg.1 v hv, hg'.1 v hv]
      exact uf_dg (A.V v) (d v) (d' v) hd hd'
  refine ⟨hbox.2.1 (fun v hv => (key v hv).1), fun g' d' hg' hd hd' => ?_⟩
  exact hbox.2.2 g' (hout g' d' hg') (fun v hv => (key v hv).2 g' d' hg' (hd v hv) (hd' v hv))

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (T : Spl B)
  {S : Finset (Plc L)} {VL : ∀ w : Plc L, Lev (Kw w)} {A : SD B.Δ}

private theorem eU_congr {K : Type} [Field K] {Δ s s' : K} (e : s = s') (h : s * s = Δ) (h' : s' * s' = Δ) :
    eU h = eU h' := by subst e; rfl

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (e : s = s') (h : s * s = Δ) (h' : s' * s' = Δ) :
    eD h = eD h' := by subst e; rfl

private theorem map_dg {k k' : Type} [Field k] [Field k'] {n : ℕ} (i : k ≃+* k') (d : Fin n → kˣ) :
    Matrix.GeneralLinearGroup.map (i : k →+* k') (diagT k (Fin n) d) =
      diagT k' (Fin n) fun a => Units.map (i : k →* k') (d a) := by
  ext a b
  simp only [Matrix.GeneralLinearGroup.map_apply, val_diagT]
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

private theorem map_inj {k k' : Type} [Field k] [Field k'] {n : ℕ} (i : k ≃+* k') :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (i : k →+* k')) := by
  intro g g' h
  ext a b
  have := congrArg (fun x : GL (Fin n) k' => (x : Matrix (Fin n) (Fin n) k') a b) h
  simpa using this

private theorem levCore (hF : Fit T S VL A) {n : ℕ} (x : UA L n) (hx : x ∈ finU (E := L) (n := n))
    (P : Pl (Lp L) → Prop) (E : ∀ v, v ∈ A.Sg → GL (Fin n) (Kv v))
    (hK : ∀ v, P v ↔ ∀ w, un w = v → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n))
    (hE : ∀ w (_ : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x = Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (E (un w) hv)) :
    ((∀ v (h : v ∈ A.Sg), E v h ∈ (A.V v).J n) ∧ ∀ v ∉ A.Sg, P v) ↔ x ∈ lev (Kall (L := L) n) S VL := by
  have memL : x ∈ lev (Kall (L := L) n) S VL ↔
      (x ∈ finU (E := L) (n := n) ∧ ∀ w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) ∧ ∀ w ∈ S, cLoc w x ∈ (VL w).J n := by
    simp [lev, Kall, Subgroup.mem_inf, Subgroup.mem_iInf]
  rw [memL]
  have loc : ∀ w (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x ∈ (VL w).J n ↔ E (un w) hv ∈ (A.V (un w)).J n := by
    intro w hw h hv
    rw [hE w hw h hv]
    exact (T w h).J _ _ (hF.c w hw) (hF.H w hw h) n _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hx, fun w => ?_⟩, fun w hw => ?_⟩
    · by_cases hv : un w ∈ A.Sg
      · obtain ⟨w0, hw0, e⟩ := (hF.sg _).1 hv
        have sp := hF.pl.split w0 hw0
        have hv0 : un w0 ∈ A.Sg := e ▸ hv
        have hk : cLoc w0 x ∈ GlobalTheory.LFun.KGL w0 (n := n) := by
          rw [hE w0 hw0 sp hv0]
          exact ((T w0 sp).K n _).2 (((Sig.finFacts _ (A.V (un w0))).2.2.2.2.2 n).2.2.2 (h1 _ hv0))
        exact (Br.uaFacts L n).2.2.2.2.2.2.2 w0 sp x hk w e.symm
      · exact (hK _).1 (h2 _ hv) w rfl
    · exact (loc w hw (hF.pl.split w hw) ((hF.sg _).2 ⟨w, hw, rfl⟩)).2 (h1 _ _)
  · rintro ⟨⟨_, h1⟩, h2⟩
    refine ⟨fun v hv => ?_, fun v _ => (hK v).2 fun w _ => h1 w⟩
    obtain ⟨w0, hw0, rfl⟩ := (hF.sg _).1 hv
    exact (loc w0 hw0 (hF.pl.split w0 hw0) hv).1 (h2 w0 hw0)

private theorem elCore (hF : Fit T S VL A) {n : ℕ} (x : UA L n) (hx : x ∈ finU (E := L) (n := n))
    (O : Pl (Lp L) → Prop) (E : ∀ v, v ∈ A.Sg → GL (Fin n) (Kv v)) (d : ParN (Lp L) n)
    (hO : ∀ v, O v ↔ ∀ w, un w = v → cLoc w x = 1)
    (hE : ∀ w (_ : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x = Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (E (un w) hv)) :
    ((∀ v (h : v ∈ A.Sg), E v h = Sig.dg (d v)) ∧ ∀ v ∉ A.Sg, O v) ↔
      OnS S x ∧ ∀ w ∈ S, ∀ h, cLoc w x = Sig.dg fun i => iu T w h (d (un w) i) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hx, fun u hu => ?_⟩, fun w hw h => ?_⟩
    · have hv : un u ∉ A.Sg := fun hv => by
        obtain ⟨w, hw, e⟩ := (hF.sg _).1 hv
        exact hu w hw e.symm
      exact (hO _).1 (h2 _ hv) u rfl
    · have hv : un w ∈ A.Sg := (hF.sg _).2 ⟨w, hw, rfl⟩
      rw [hE w hw h hv, h1 _ hv]
      exact map_dg (T w h).i (d (un w))
  · rintro ⟨⟨_, h1⟩, h2⟩
    refine ⟨fun v hv => ?_, fun v hv => (hO v).2 fun w e => h1 w fun w' hw' e' => hv ?_⟩
    · obtain ⟨w0, hw0, rfl⟩ := (hF.sg _).1 hv
      have sp := hF.pl.split w0 hw0
      apply map_inj (T w0 sp).i
      rw [← hE w0 hw0 sp hv, h2 w0 hw0 sp]
      exact (map_dg (T w0 sp).i (d (un w0))).symm
    · exact (hF.sg _).2 ⟨w', hw', by rw [← e', e]⟩

private theorem expo_map {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (habs : ∀ (z : ℂ) (a : kˣ), absPow k' z (Units.map (i : k →* k') a) = absPow k z a)
    {n : ℕ} (ψ : Fin n → k'ˣ →* ℂˣ) (d : Fin n → kˣ) :
    Dict.expo ψ (fun a => Units.map (i : k →* k') (d a)) = Dict.expo (fun a => (ψ a).comp (Units.map (i : k →* k'))) d := by
  have hdet : ∀ {R : Type} [CommRing R] (t : Fin n → Rˣ) (a : Fin n),
      Matrix.GeneralLinearGroup.det ((leviTorus R (Fin n)) t a) = t a := fun t a =>
    congrFun ((leviTorus _ (Fin n)).symm_apply_apply t) a
  have h1 : torusChar ψ (fun a => Units.map (i : k →* k') (d a)) =
      torusChar (fun a => (ψ a).comp (Units.map (i : k →* k'))) d := by
    simp [torusChar_apply]
  have h2 : ((deltaHalf k' fun _ : Fin n => Unit).comp (leviTorus k' (Fin n)).toMonoidHom)
        (fun a => Units.map (i : k →* k') (d a)) =
      ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) d := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, deltaHalf_apply, deltaHalf_apply]
    refine Finset.prod_congr rfl fun a _ => ?_
    have e1 := hdet (fun a => Units.map (i : k →* k') (d a)) a
    have e2 := hdet d a
    simp only [MulEquiv.coe_toMonoidHom]
    rw [e1, e2]
    exact habs _ _
  simp only [Dict.expo]
  rw [h1, h2]

end SlopeTestRemainingChoices

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (hB : B.Ok) (T : Spl B)
  {S : Finset (Plc L)} {VL : ∀ w : Plc L, Lev (Kw w)} {A : SD B.Δ} (hF : Fit T S VL A)

include hB hF in
private theorem hsG (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg) (g : GA B.Δ) :
    cLoc w (B.bG g : UA L 3) =
      Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (eU (A.hs _ hv) (g.1 (un w))) := by
  rw [hB.splG w (T w h) g, eU_congr (hF.s w hw h) (A.hs _ hv) (T w h).hs]

include hB hF in
private theorem hsS (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg) (g : SA B.Δ) :
    cLoc w (B.bS g : UA L 2) =
      Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (eD (A.hs _ hv) ((g : DA B.Δ).1 (un w))) := by
  rw [hB.splS w (T w h) g, eD_congr (hF.s w hw h) (A.hs _ hv) (T w h).hs]

private theorem hfS (g : SA B.Δ) : (B.bS g : UA L 2) ∈ finU (E := L) (n := 2) := (B.bS g).2.1

include hB hF in
private theorem cl1 (hA : A.Ok) (g : GA B.Δ) : g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall (L := L) 3) S VL :=
  ((datOk _ _ A hA).2.2.2.1 g).trans (levCore T hF _ (B.bG g).2 (fun v => g.1 v ∈ KU (Ov v) _)
    (fun v h => eU (A.hs v h) (g.1 v)) (fun v => hB.KG g v) (fun w hw h hv => hsG hB T hF w hw h hv g))

include hB hF in
private theorem cl2 (hA : A.Ok) (g : SA B.Δ) :
    (g : DA B.Δ) ∈ A.dat.U2 ↔ (B.bS g : UA L 2) ∈ lev (Kall (L := L) 2) S VL :=
  ((datOk _ _ A hA).2.2.2.2 (g : DA B.Δ)).trans (levCore T hF _ (hfS g) (fun v => (g : DA B.Δ).1 v ∈ KD _ (Ov v))
    (fun v h => eD (A.hs v h) ((g : DA B.Δ).1 v)) (fun v => hB.KS g v) (fun w hw h hv => hsS hB T hF w hw h hv g))

include hB hF in
private theorem cl3 (g : GA B.Δ) (d : ParN (Lp L) 3) : A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧
    ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i) :=
  elCore T hF _ (B.bG g).2 (fun v => g.1 v = 1) (fun v h => eU (A.hs v h) (g.1 v)) d (fun v => hB.oneG g v)
    (fun w hw h hv => hsG hB T hF w hw h hv g)

include hB hF in
private theorem cl4 (g : SA B.Δ) (d : ParN (Lp L) 2) : A.IsElD g d ↔ OnS S (B.bS g : UA L 2) ∧
    ∀ w ∈ S, ∀ h, cLoc w (B.bS g : UA L 2) = Sig.dg fun i => iu T w h (d (un w) i) :=
  elCore T hF _ (hfS g) (fun v => (g : DA B.Δ).1 v = 1) (fun v h => eD (A.hs v h) ((g : DA B.Δ).1 v)) d
    (fun v => hB.oneS g v) (fun w hw h hv => hsS hB T hF w hw h hv g)

end Main


theorem levG : LevG := by
  intro L _ _ _ B hB T S VL A hA hF
  refine ⟨?_, ?_, ?_, ?_, fun w h n ψ d _ => expo_map (T w h).i (T w h).abs ψ d⟩
  · with_reducible exact cl1 hB T hF hA
  · with_reducible exact cl2 hB T hF hA
  · with_reducible exact cl3 hB T hF
  · with_reducible exact cl4 hB T hF

end UpperTheory.V.Z.Sym.So

end
end
