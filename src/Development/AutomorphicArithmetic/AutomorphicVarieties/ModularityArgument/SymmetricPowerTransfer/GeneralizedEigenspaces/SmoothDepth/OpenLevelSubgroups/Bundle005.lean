module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle004
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle004
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
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.CofinalityAlt

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GLnLocal

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private noncomputable abbrev fp (x : UA L n) : GL (Fin n) (Af L) :=
  Matrix.GeneralLinearGroup.map (pFin L) (x : GA L n)

private theorem cont_fp : Continuous (fp : UA L n → GL (Fin n) (Af L)) :=
  continuous_mapFin.comp continuous_subtype_val

private theorem e_apply (w : Plc L) (x : UA L n) : finiteRestrictedEquiv L n (fp x) w = cLoc w x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [finiteRestrictedEquiv_apply]
  rfl

private theorem cont_cLoc (w : Plc L) : Continuous (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) := by
  have e : (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) =
      fun x => finiteRestrictedEquiv L n (fp x) w := funext fun x => (e_apply w x).symm
  rw [e]
  exact (RestrictedProduct.continuous_eval w).comp ((finiteRestrictedEquiv L n).continuous.comp cont_fp)

private theorem snd_eq (x : UA L n) : (prodEquiv L n (x : GA L n)).2 = fp x :=
  Units.ext (Matrix.ext fun a b => by rw [prodEquiv_apply_snd]; rfl)

private theorem fst_eq (x : finU (E := L) (n := n)) : (prodEquiv L n ((x : UA L n) : GA L n)).1 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [prodEquiv_apply_fst]
  have key := congrArg (fun g : GL (Fin n) (Cinf L) => g.1 a b) (MonoidHom.mem_ker.1 x.2)
  refine (infEq L).symm.injective (key.trans ?_)
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

private theorem mem_Kall {x : UA L n} :
    x ∈ Kall L n ↔ x ∈ finU (E := L) (n := n) ∧ ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) := by
  simp [Kall, Subgroup.mem_inf, Subgroup.mem_iInf]

private theorem exists_open {U : Subgroup (UA L n)} (hU : IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U}) :
    ∃ O : Set (GL (Fin n) (Af L)), IsOpen O ∧ 1 ∈ O ∧ ∀ x : finU (E := L) (n := n), fp x.1 ∈ O → (x : UA L n) ∈ U := by
  obtain ⟨A, hA, eA⟩ := isOpen_induced_iff.1 hU
  obtain ⟨B, hB, rfl⟩ := isOpen_induced_iff.1 hA
  let c : GL (Fin n) (Af L) → GA L n := fun k => (prodEquiv L n).symm (1, k)
  have hc : Continuous c := (prodEquiv L n).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hx : ∀ x : finU (E := L) (n := n), c (fp x.1) = ((x : UA L n) : GA L n) := fun x => by
    change (prodEquiv L n).symm _ = _
    rw [← fst_eq x, ← snd_eq]
    exact (prodEquiv L n).symm_apply_apply _
  have hmem : ∀ x : finU (E := L) (n := n), (x : UA L n) ∈ U ↔ ((x : UA L n) : GA L n) ∈ B := fun x =>
    (Set.ext_iff.1 eA x).symm
  refine ⟨c ⁻¹' B, hB.preimage hc, ?_, fun x hx' => ?_⟩
  · have h := hx 1
    have h1 : fp ((1 : finU (E := L) (n := n)) : UA L n) = 1 := map_one _
    rw [h1] at h
    rw [Set.mem_preimage, h]
    exact (hmem 1).1 (one_mem U)
  · rw [Set.mem_preimage, hx] at hx'
    exact (hmem x).2 hx'

private theorem nbhd {O : Set (GL (Fin n) (Af L))} (hO : IsOpen O) (h1 : 1 ∈ O) :
    ∃ T : Finset (Plc L), ∀ g : GL (Fin n) (Af L), g ∈ integralFiniteGL L n →
      (∀ v ∈ T, finiteRestrictedEquiv L n g v = 1) → g ∈ O := by
  let e := finiteRestrictedEquiv L n
  let s := RestrictedProduct.structureMap (fun v : Plc L => GL (Fin n) (v.adicCompletion L))
    (fun v => (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) Filter.cofinite
  have hs : Continuous fun a => e.symm (s a) :=
    e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous
  have hone : e.symm (s fun v => ⟨1, one_mem _⟩) = 1 := by
    have : s (fun v => ⟨1, one_mem _⟩) = 1 := rfl
    rw [this, map_one]
  obtain ⟨T, u, hu, hT⟩ := isOpen_pi_iff.1 (hO.preimage hs) (fun v => ⟨1, one_mem _⟩)
    (by rw [Set.mem_preimage, hone]; exact h1)
  refine ⟨T, fun g hg hgT => ?_⟩
  have hint := (mem_integralFiniteGL_iff_forall L n).1 hg
  have hg' : e.symm (s fun v => ⟨e g v, hint v⟩) = g := by
    have : s (fun v => ⟨e g v, hint v⟩) = e g := by
      ext v
      rfl
    rw [this, e.symm_apply_apply]
  rw [← hg']
  refine hT fun v hv => ?_
  have : (⟨e g v, hint v⟩ : (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) = ⟨1, one_mem _⟩ :=
    Subtype.ext (hgT v hv)
  rw [this]
  exact (hu v hv).2

private theorem fp_mem {x : UA L n} (hx : ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) :
    fp x ∈ integralFiniteGL L n :=
  (mem_integralFiniteGL_iff_forall L n).2 fun v => by
    rw [e_apply]
    exact GlobalTheory.StabInt.mem_integralGL_of_mem_KGL (hx v)

private theorem clause1 (U : Subgroup (UA L n)) (hU : IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U}) :
    ∃ T : Finset (Plc L), Kall L n ⊓ ⨅ w ∈ T, away n w ≤ U := by
  obtain ⟨O, hO, h1, hOU⟩ := exists_open hU
  obtain ⟨T, hT⟩ := nbhd hO h1
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hf, hi⟩ := mem_Kall.1 hK
  refine hOU ⟨x, hf⟩ (hT _ (fp_mem hi) fun v hv => ?_)
  rw [e_apply]
  have h := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hA v) hv
  exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h v) rfl)

private theorem clause2 : IsLevel (Kall L n) := by
  refine ⟨le_rfl, ?_⟩
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ Kall L n} =
      (fun x : finU (E := L) (n := n) => fp x.1) ⁻¹' (integralFiniteGL L n : Set (GL (Fin n) (Af L))) := by
    ext x
    refine ⟨fun h => fp_mem (mem_Kall.1 h).2, fun h => mem_Kall.2 ⟨x.2, fun w => ?_⟩⟩
    have h' := (mem_integralFiniteGL_iff_forall L n).1 h w
    rw [e_apply] at h'
    exact GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h'
  rw [e]
  exact (isOpen_integralFiniteGL L n).preimage (cont_fp.comp continuous_subtype_val)

private theorem clause3 (U : Subgroup (UA L n)) (hU : IsLevel U) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) : IsLevel (lev U S V) := by
  refine ⟨inf_le_left.trans hU.1, ?_⟩
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ lev U S V} = {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∩
      ⋂ w ∈ S, (fun x : finU (E := L) (n := n) => cLoc w (x : UA L n)) ⁻¹' ((V w).J n : Set (GL (Fin n) (Kw w))) := by
    ext x
    simp [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  rw [e]
  exact hU.2.inter (isOpen_biInter_finset fun w _ =>
    ((Sig.finFacts _ (V w)).2.2.2.2.2 n).2.1.preimage ((cont_cLoc w).comp continuous_subtype_val))

private theorem clause4 (U : Subgroup (UA L n)) (hU : IsLevel U) :
    ∀ᶠ w : Plc L in Filter.cofinite, locU n w ⊓ Kall L n ≤ U := by
  obtain ⟨T, hT⟩ := clause1 U hU.2
  have hfin : ∀ t : Plc L, {w : Plc L | w.under (𝓞 (Lp L)) = t.under (𝓞 (Lp L))}.Finite := fun t =>
    ((IsDedekindDomain.primesOver_finite (t.under (𝓞 (Lp L))).asIdeal (𝓞 L)).preimage
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset
      fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Filter.eventually_cofinite.2 ((T.finite_toSet.biUnion fun t _ => hfin t).subset fun w hw => ?_)
  by_contra hn
  refine hw fun x hx => hT ?_
  obtain ⟨hl, hK⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hK, Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht =>
    Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
  refine Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hl).2 u) fun huw => hn ?_
  exact Set.mem_biUnion (Finset.mem_coe.2 ht) (huw.symm.trans hu)

end UpperTheory.V.Z.Sym.Al.CofinalityAlt

open UpperTheory.V.Z.Sym.Al.CofinalityAlt in
theorem UpperTheory.V.Z.Sym.Al.cof :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ),
        (∀ U : Subgroup (UA L n), IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} → ∃ T : Finset (Plc L), Kall L n ⊓ ⨅ w ∈ T, away n w ≤ U) ∧
        IsLevel (Kall L n) ∧ (∀ U : Subgroup (UA L n), IsLevel U → ∀ S V, IsLevel (lev U S V)) ∧
        ∀ U : Subgroup (UA L n), IsLevel U → ∀ᶠ w : Plc L in Filter.cofinite, locU n w ⊓ Kall L n ≤ U := by
  intro L _ _ _ n
  exact ⟨clause1, clause2, clause3, clause4⟩
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem thinOut {α β : Type} [DecidableEq α] (f : α → β) (S T : Finset α) (hinj : Set.InjOn f (S : Set α)) :
    ∃ T' : Finset α, S ⊆ T' ∧ Set.InjOn f (T' : Set α) ∧ (∀ t ∈ T', t ∉ S → ∀ s ∈ S, f s ≠ f t) ∧
      ∀ t ∈ T, ∃ t' ∈ T', f t' = f t := by
  induction T using Finset.induction_on with
  | empty => exact ⟨S, subset_rfl, hinj, fun t h h' => absurd h h', by simp⟩
  | insert a T₀ _ ih =>
    obtain ⟨T', h1, h2, h3, h4⟩ := ih
    by_cases h : ∃ t' ∈ T', f t' = f a
    · refine ⟨T', h1, h2, h3, fun t ht => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact h
      · exact h4 t ht
    · push Not at h
      refine ⟨insert a T', h1.trans (Finset.subset_insert _ _), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h₁ | h₁ <;>
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h₂ | h₂
        · rw [h₁, h₂]
        · subst h₁
          exact absurd hxy.symm (h y h₂)
        · subst h₂
          exact absurd hxy (h x h₁)
        · exact h2 h₁ h₂ hxy
      · intro t ht htS s hs
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact h s (h1 hs)
        · exact h3 t ht htS s hs
      · intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact ⟨_, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨t', a', b⟩ := h4 t ht
          exact ⟨t', Finset.mem_insert_of_mem a', b⟩

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem away_congr {n : ℕ} {w w' : Plc L} (h : w.under (𝓞 (Lp L)) = w'.under (𝓞 (Lp L))) :
    away n w = away n w' := by
  simp only [away, h]

private theorem cLoc_away {n : ℕ} {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl

private noncomputable def AT (S : Finset (Plc L)) (W : ∀ w : Plc L, Sig.Lev (Kw w)) (T : Finset (Plc L)) : Subgroup (UA L 2) :=
  lev (Kall (L := L) 2) S W ⊓ ⨅ w ∈ T, away 2 w

open GlobalTheory.SplitPts in
private theorem step [DecidableEq (Plc L)] {V : Type} [AddCommGroup V] [Module ℂ V] (S T₀ : Finset (Plc L))
    (W : ∀ w : Plc L, Sig.Lev (Kw w)) (w : Plc L)
    (hS : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (hT : ∀ t ∈ T₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (φ φ' : UA L 2 → V)
    (hspan : InSpan w φ φ') (hAF : IsAF R (AT S W (insert w T₀)) φ)
    (hinv : ∀ x ∈ locU 2 w, x ∈ Kall (L := L) 2 → (w ∈ S → cLoc w x ∈ (W w).J 2) → ∀ g, φ' (g * x) = φ' g) :
    IsAF R (AT S W T₀) φ' := by
  have h1 : AT S W (insert w T₀) ≤ away 2 w :=
    inf_le_right.trans (iInf₂_le w (Finset.mem_insert_self _ _))
  have h2 := (spanKeep L 2 V w φ φ' hspan).2.1 R _ h1 hAF
  have hLocAway (v t : Plc L) (h : v.under (𝓞 (Lp L)) ≠ t.under (𝓞 (Lp L))) :
      locU 2 v ≤ away 2 t := by
    intro x hx
    refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
      (by rw [hu]; exact h.symm)
  have hSplit (g : UA L 2) : ∃ x ∈ locU 2 w, ∃ y ∈ away 2 w, g = x * y := by
    classical
    let P (u : Plc L) := u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    let e : Af L :=
      ⟨fun u => if P u then 1 else 0, Filter.Eventually.of_forall fun u => by
        dsimp only
        split_ifs
        · exact one_mem _
        · exact zero_mem _⟩
    let cut (A : Matrix (Fin 2) (Fin 2) (Af L)) := e • A + (1 - e) • 1
    have hpos (A : Matrix (Fin 2) (Fin 2) (Af L)) (u : Plc L) (hu : P u) :
        RingHom.mapMatrix (pLoc L u) (cut A) = RingHom.mapMatrix (pLoc L u) A := by
      have he : pLoc L u e = 1 := ite_eq_left hu
      ext i j
      simp [cut, Matrix.add_apply, Matrix.smul_apply, he]
    have hneg (A : Matrix (Fin 2) (Fin 2) (Af L)) (u : Plc L) (hu : ¬ P u) :
        RingHom.mapMatrix (pLoc L u) (cut A) = 1 := by
      have he : pLoc L u e = 0 := ite_eq_right hu
      refine Matrix.ext fun i j => ?_
      change pLoc L u (e * A i j + (1 - e) * (1 : Matrix (Fin 2) (Fin 2) (Af L)) i j) =
        (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion L)) i j
      rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, he, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hmul {A B : Matrix (Fin 2) (Fin 2) (Af L)} (h : A * B = 1) :
        cut A * cut B = 1 := by
      refine matAf_ext fun u => ?_
      rw [map_mul, map_one]
      by_cases hu : P u
      · rw [hpos _ _ hu, hpos _ _ hu, ← map_mul, h, map_one]
      · rw [hneg _ _ hu, hneg _ _ hu, one_mul]
    let a := Matrix.GeneralLinearGroup.map (pFin L) g.1
    let k : GL (Fin 2) (Af L) :=
      ⟨cut a.val, cut (a⁻¹).val, hmul (by simp), hmul (by simp)⟩
    have hcomp (u : Plc L) (hu : P u) :
        Matrix.GeneralLinearGroup.map (pLoc L u) k = cLoc u g :=
      Units.ext (hpos _ _ hu)
    have hzero (u : Plc L) (hu : ¬ P u) :
        Matrix.GeneralLinearGroup.map (pLoc L u) k = 1 :=
      Units.ext (hneg _ _ hu)
    have hmem : finGL L 2 k ∈ UA L 2 := by
      refine finGL_mem_UA k fun u => ?_
      have hconj : (conjSrc (conjE L) u).under (𝓞 (Lp L)) = u.under (𝓞 (Lp L)) :=
        (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
          (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) u _).2
          (Or.inr (conjPl_self_conjSrc u))
      by_cases hu : P u
      · rw [hcomp u hu, hcomp _ (hconj.trans hu)]
        exact comp_eq g u
      · rw [hzero u hu, hzero _ (fun h => hu (hconj.symm.trans h))]
        simp
    let x : UA L 2 := ⟨_, hmem⟩
    have hloc (u : Plc L) : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) k := by
      change Matrix.GeneralLinearGroup.map ((pLoc L u).comp (pFin L)) (finGL L 2 k) = _
      exact Units.ext (congrArg (fun M : GL (Fin 2) (Af L) => RingHom.mapMatrix (pLoc L u) M.val) (pFin_finGL k))
    refine ⟨x, Subgroup.mem_inf.2 ⟨pInf_finGL k, ?_⟩, x⁻¹ * g, ?_, by group⟩
    · refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_
      exact MonoidHom.mem_ker.2 ((hloc u).trans (hzero u hu))
    · refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_
      rw [map_mul, map_inv, hloc u, hcomp u hu, inv_mul_cancel]
  have hIntegral {x y : UA L 2} (hx : x ∈ locU 2 w) (hy : y ∈ away 2 w)
      (hxy : x * y ∈ Kall (L := L) 2) :
      x ∈ Kall (L := L) 2 ∧ y ∈ Kall (L := L) 2 := by
    have hxinf : cInf x = 1 := (Subgroup.mem_inf.1 hx).1
    have hyinf : cInf (x * y) = 1 := (Subgroup.mem_inf.1 hxy).1
    rw [map_mul, hxinf, one_mul] at hyinf
    have hLoc (u : Plc L) :
        cLoc u x ∈ GlobalTheory.LFun.KGL u (n := 2) ∧
        cLoc u y ∈ GlobalTheory.LFun.KGL u (n := 2) := by
      have huK := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hxy).2 u)
      by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · have hyu : cLoc u y = 1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy u) hu
        rw [map_mul, hyu, mul_one] at huK
        exact ⟨huK, hyu.symm ▸ one_mem _⟩
      · have hxu : cLoc u x = 1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu
        rw [map_mul, hxu, one_mul] at huK
        exact ⟨hxu.symm ▸ one_mem _, huK⟩
    exact ⟨Subgroup.mem_inf.2 ⟨hxinf, Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 (hLoc u).1⟩,
      Subgroup.mem_inf.2 ⟨hyinf, Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 (hLoc u).2⟩⟩
  refine ⟨h2.left, h2.inf, ?_⟩
  intro u hu g
  obtain ⟨x, hx, y, hy, rfl⟩ := hSplit u
  obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hK, hJ⟩ := Subgroup.mem_inf.1 hlev
  have hxy := hIntegral hx hy hK
  have hJ' : ∀ v ∈ S, cLoc v (x * y) ∈ (W v).J 2 := fun v hv =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hJ v) hv
  have hyw : cLoc w y = 1 := cLoc_away hy
  have hyA : y ∈ AT S W (insert w T₀) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxy.2, ?_⟩, ?_⟩
    · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
      show cLoc v y ∈ (W v).J 2
      by_cases hvw : v = w
      · subst hvw
        rw [hyw]
        exact one_mem _
      · have hxv : cLoc v x = 1 :=
          cLoc_away (hLocAway w v (hS v hv hvw).symm hx)
        have := hJ' v hv
        rwa [map_mul, hxv, one_mul] at this
    · refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hy
      · have hxt : x ∈ away 2 t := hLocAway w t (hT t ht).symm hx
        have hxyt : x * y ∈ away 2 t := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t) ht
        exact (Subgroup.mul_mem_cancel_left _ hxt).1 hxyt
  rw [← mul_assoc, h2.level y hyA, hinv x hx hxy.1 ?_]
  intro hwS
  have := hJ' w hwS
  rwa [map_mul, hyw, mul_one] at this

end
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.raise :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π →
        ∀ U : Subgroup (UA L n), U ≤ Kall (L := L) n → ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w ∈ S, locU n w ⊓ Kall (L := L) n ≤ U ∧ IsUnramU π w) → ∀ (W : ∀ w : Plc L, Sig.Lev (Kw w)) (φ : UA L n → V), φ ≠ 0 → CoefIn φ π →
        IsAF R (lev U S W) φ → ∃ φ' : UA L n → V, φ' ≠ 0 ∧ CoefIn φ' π ∧ IsAF R U φ' := by
  classical
  intro L _ _ _ n V _ _ _ R π hπ U hU S
  induction S using Finset.induction_on with
  | empty => exact fun _ _ W φ h0 hc h => ⟨φ, h0, hc, h.left, h.inf, fun u hu => h.level u (by simpa [lev] using hu)⟩
  | insert w S hw ih =>
    intro hS hK W φ h0 hc h
    have hwm : w ∈ insert w S := Finset.mem_insert_self _ _
    obtain ⟨φ', a0, a1, a2⟩ := spanSph L n V π hπ w (hK w hwm).2 φ h0 hc
    obtain ⟨k1, k2, -⟩ := spanKeep L n V w φ φ' a1
    have hA : IsAF R (lev U S W ⊓ away n w) φ' := k2 R _ inf_le_right ⟨h.left, h.inf, fun u hu => h.level u (by
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu
      simp only [lev, away, Subgroup.mem_inf, Subgroup.mem_iInf] at h1 h2 ⊢
      refine ⟨h1.1, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.1 hw' with rfl | hw'
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (h2 w' rfl)]; exact one_mem _
      · exact h1.2 w' hw')⟩
    refine ih ⟨fun u hu => hS.split u (Finset.mem_insert_of_mem hu), hS.inj.mono (by simp)⟩
      (fun u hu => hK u (Finset.mem_insert_of_mem hu)) W φ' a0 (k1 π hπ hc) ⟨hA.left, hA.inf, fun u hu g => ?_⟩
    obtain ⟨-, f2, -, -, -, f6⟩ := factor L n w
    obtain ⟨x, hx, y, hy, rfl⟩ := f2 u
    have hxK : x ∈ Kall (L := L) n := ((f6 x hx y hy).1 (hU hu.1)).1
    have hxl : x ∈ lev U S W := by
      simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine ⟨(hK w hwm).1 ⟨hx, hxK⟩, fun w' hw' => ?_⟩
      have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun e =>
        hw (hS.inj (Finset.mem_coe.2 hwm) (Finset.mem_coe.2 (Finset.mem_insert_of_mem hw')) e ▸ hw')
      have := (factor L n w').2.2.1 w hne hx
      simp only [away, Subgroup.mem_iInf] at this
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (this w' rfl)]
      exact one_mem _
    have hyl : y ∈ lev U S W := (Subgroup.mul_mem_cancel_left _ hxl).1 hu
    rw [← mul_assoc, hA.level y ⟨hyl, hy⟩, a2 x ⟨hx, hxK⟩]
end
