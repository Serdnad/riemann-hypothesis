module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostUnitAddConjEqOne
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle298
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

section

noncomputable section

namespace GlobalTheory.GalOne.IoCmp

section Letters

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem letter_relab {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {σ : c.F →+* ℂ}
    {X : Data E r} {g q0 n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (Dc : Dic Dw c σ X g q0 n a)
    (hm : ∀ τ, Formalism.L2.PjFree.relab c σ τ ∉ X.Ψ → Dw.mult τ ≤ X.p0) (ℓ : Formalism.L2.Pj.LtN Dw n) :
    (Dc.eL ℓ).2.2 = ℓ.2.2 ∧
      ((∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ Formalism.L2.PjFree.relab c σ ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨
       (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ Formalism.L2.PjFree.relab c σ ℓ.1 = conjEmb (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1)) := by
  have hd := Dc.dir_eq ℓ
  generalize Dc.eL ℓ = L at hd ⊢
  obtain ⟨t, ρ, b⟩ := L
  obtain ⟨τ, i, b'⟩ := ℓ
  simp only [letterDir] at hd ⊢
  have hb : b = b' := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    simp [Pi.single_eq_of_ne hne] at this
  subst hb
  have hj : Dc.idx.symm (rowOf X Dc.hr (t, ρ)) = Dc.e.symm ⟨τ, i⟩ := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  have hi : Dc.idx (Dc.e.symm ⟨τ, i⟩) = (t, rowIdx Dc.hr ρ) := by rw [← hj, Equiv.apply_symm_apply]; rfl
  have hty := Dc.ty_eq (Dc.e.symm ⟨τ, i⟩)
  have hper : ∀ x v, per X x v (t, rowIdx Dc.hr ρ) = Formalism.L2.Pj.perFr X x v (Formalism.L2.PjFree.relab c σ τ) i := fun x v => by
    have := Dc.per_eq x v (Dc.e.symm ⟨τ, i⟩)
    rwa [pv, Function.comp_apply, hi, Equiv.apply_symm_apply] at this
  rw [hi, Equiv.apply_symm_apply] at hty
  refine ⟨rfl, ?_⟩
  rcases ρ with k | k
  · have h1 : Formalism.L2.PjFree.relab c σ τ = t.1 := hty.symm.trans (rowType_rowOf_inl X Dc.hr t k)
    rw [h1] at hper
    have h2 := coord_eq_of_per_mem X t _ (by simp) i hper
    rw [rowIdx_inl] at h2
    exact Or.inl ⟨k, rfl, h1, by omega⟩
  · have h1 : Formalism.L2.PjFree.relab c σ τ = conjEmb t.1 := hty.symm.trans (rowType_rowOf_inr X Dc.hr t k)
    rw [h1] at hper
    have hk := k.2
    have h2 := coord_eq_of_per_conj X t _ (by rw [rowIdx_inr]; omega) i hper
    rw [rowIdx_inr] at h2
    have h3 := hm τ (by rw [h1]; exact (X.cmType t.1).1 t.2)
    have h4 : (i : ℕ) < X.p0 := lt_of_lt_of_le i.2 h3
    exact Or.inr ⟨k, rfl, h1, by omega⟩

end Letters

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
open GlobalTheory.OneMapRef.IoCmp

end GlobalTheory.GalOne.IoCmp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.DilateLevel

open GlobalTheory.Dict.MarkMove

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem level_smul_levQ (q : LevQ Dw l) : l.M • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (level_mem l).1 trivial

theorem cSep_smul_levQ (q : LevQ Dw l) : cSep l • q = q := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have e : cSep l • y - y = (cSep l - 1) • y := by rw [sub_smul, one_smul]
  rw [e]
  exact Submodule.smul_mem_smul (cSep_spec l).2 trivial

theorem sub_sepRep (q : LevQ Dw l) (x : Dw.La) (hx : x ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (hq : Submodule.Quotient.mk x = q) : ∃ z : Dw.La, x - cSep l • levRep q = l.M • z := by
  have h1 : x - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
    (Submodule.Quotient.eq _).1 (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)).symm)
  obtain ⟨b1, hb1⟩ := modN_smul l ((mul_comm _ _).trans l.prod) (cSep_spec l).1 h1
  obtain ⟨b2, hb2⟩ := modN_smul l l.prod (cSep_spec l).2 hx
  refine ⟨b1 - b2, ?_⟩
  rw [smul_sub, ← hb1, ← hb2, smul_sub, sub_smul, one_smul]
  abel

end GlobalTheory.DilateLevel

namespace GlobalTheory.DilateLevel

open GlobalTheory.Dict.MarkMove

theorem dilate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (r n : ℕ) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (m : ℤ), IsCoprime m (l.M : ℤ) → (IsMark l L mk → IsMark l L (m • mk)) ∧ ∀ (N : ℕ) (Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E), ((∀ a, mk a ∈ L) → IsRoots l L mk N Y → IsRoots l L (m • mk) N (fun q => Y (m • q))) ∧ ∀ (g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (w : E) (Λ : Lt E n) (v : TF n g) (c : (Fin n → LevQ Dw l) → ℂ), gphi X bas w Λ L v (fun q => c (m • q)) (fun q => Y (m • q)) = gphi X bas w Λ L v c Y := by
  intro E _ _ _ H Dw l r n L mk m hm
  refine hm.elim fun α hβ => hβ.elim fun β hab => ?_
  have hM0 : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hsm : ∀ a, (m • mk) a = m • mk a := fun a => LinearMap.smul_apply _ _ _
  have hbez : ∀ x : Fin r → E, x = α • (m • x) + β • (l.M • x) := fun x => by
    rw [smul_smul, ← natCast_zsmul, smul_smul, ← add_smul, hab, one_smul]
  refine ⟨fun h => ?_, fun N Y => ⟨fun hmem h => ?_, fun g X bas w Λ v c => ?_⟩⟩
  · refine ⟨fun a => by rw [hsm]; exact zsmul_mem (h.mem a) m, fun a ha hu => ?_, fun v hv => ?_⟩
    · refine hu.elim fun u hu' => h.inj a ha ⟨α • u + β • mk a, add_mem (zsmul_mem hu'.1 α) (zsmul_mem (h.mem a) β), ?_⟩
      have e : m • mk a = l.M • u := (hsm a).symm.trans hu'.2
      refine (hbez (mk a)).trans ?_
      rw [e, smul_add, smul_comm α, smul_comm β]
    · have hvL : v ∈ L := Submodule.smul_le_right hv
      refine (h.surj (α • v) (zsmul_mem hv α)).elim fun a1 h1 => h1.elim fun ha1 h2 => h2.elim fun u1 h3 => ?_
      refine ⟨a1, ha1, m • u1 + β • v, add_mem (zsmul_mem h3.1 m) (zsmul_mem hvL β), ?_⟩
      have e : α • v = mk a1 + l.M • u1 := h3.2
      refine (hbez v).trans ?_
      rw [smul_comm α m, e, hsm, smul_add, smul_add, smul_comm m, smul_comm β]
      abel
  · intro q b
    have h0 := h (m • q) b
    refine ⟨?_, h0.2⟩
    refine h0.1.elim fun a0 k => k.elim fun ha0 k2 => ?_
    have hq0 : Submodule.Quotient.mk a0 = m • q b := k2.1
    have hY0 := k2.2
    set a' : Dw.La := cSep l • levRep (q b) with ha'
    have ha'm : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul (cSep_spec l).1 trivial
    have hcls : (Submodule.Quotient.mk a' : LevQ Dw l) = q b := by
      have hr : (Submodule.Quotient.mk (levRep (q b)) : LevQ Dw l) = q b :=
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))
      rw [ha', Submodule.Quotient.mk_smul, hr, cSep_smul_levQ]
    refine ⟨a', ha'm, hcls, ?_⟩
    have hm' : (Submodule.Quotient.mk (m • a') : LevQ Dw l) = m • q b := by
      rw [Submodule.Quotient.mk_smul, hcls]
    refine (sub_sepRep (m • q b) a0 ha0 hq0).elim fun z1 hz1 => ?_
    refine (sub_sepRep (m • q b) (m • a') (zsmul_mem ha'm m) hm').elim fun z2 hz2 => ?_
    have hd : a0 - m • a' = l.M • (z1 - z2) := by
      rw [smul_sub, ← hz1, ← hz2]; abel
    have key : ((l.M : E)⁻¹) • (mk a0 - (m • mk) a') = mk (z1 - z2) := by
      rw [hsm, ← map_zsmul mk, ← map_sub, hd, map_nsmul, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM0]
    have := add_mem hY0 (hmem (z1 - z2))
    rw [← key] at this
    convert this using 1
    rw [smul_sub]
    abel
  · have hk : ∀ q : Fin n → LevQ Dw l, ((l.M : ℤ)) • q = 0 := fun q => funext fun b => by
      rw [Pi.smul_apply, natCast_zsmul, level_smul_levQ]; rfl
    have hinv : ∀ q : Fin n → LevQ Dw l, α • m • q = q := fun q => by
      rw [smul_smul, show α * m = 1 - β * l.M by linear_combination hab, sub_smul, one_smul, mul_smul, hk,
        smul_zero, sub_zero]
    let e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l) :=
      { toFun := fun q => m • q
        invFun := fun q => α • q
        left_inv := fun q => hinv q
        right_inv := fun q => by
          change m • α • q = q
          rw [smul_comm]; exact hinv q }
    exact finsum_comp_equiv e (f := fun q => c q • heisG X bas (Y q) (projA X bas w (tens Λ L) v))

end GlobalTheory.DilateLevel
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
noncomputable section

namespace GlobalTheory.LocNorm

theorem good_eventually : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (κ : Type) (bL : Module.Basis κ ℚ L) (θ : L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      Valued.v (2 : v.adicCompletion ℚ) = 1 ∧ IsIntB v bL 1 ∧
      (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) ∧
      (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) ∧
      (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      (∀ x, IsSmallB v bL x → IsSmallB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ) ∧ IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ⁻¹) := by
  intro L _ _ c κ bL θ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have ev := fun (q : ℚ) => rat_mem_adicCompletionIntegers_eventually q
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (bL t.1 * bL t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (c (bL t.1)) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hl : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Fin 3 × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (![1, θ, θ⁻¹] t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hfin := Filter.eventually_cofinite.1 (((hc.and hs).and hl).and (ev (1 / 2)))
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨⟨⟨hcv, hsv⟩, hlv⟩, h2v⟩ := hv
  have hmem : ∀ a : v.adicCompletion ℚ, a ∈ v.adicCompletionIntegers ℚ ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hint : ∀ ℓ : L, (∀ k, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr ℓ k) ∈ v.adicCompletionIntegers ℚ) →
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ℓ) := by
    intro ℓ hℓ k
    rw [repr_tmul_apply, one_mul]; exact hℓ k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hint θ (fun k => hlv (1, k)), hint θ⁻¹ (fun k => hlv (2, k))⟩
  · have hle : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by
      have h := (v.adicCompletionIntegers ℚ).add_mem 1 1 (one_mem _) (one_mem _)
      rw [one_add_one_eq_two] at h
      exact (hmem _).1 h
    have hle' : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) ≤ 1 := (hmem _).1 h2v
    have hprod : Valued.v (2 : v.adicCompletion ℚ) * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) = 1 := by
      rw [← map_mul, show (2 : v.adicCompletion ℚ) * algebraMap ℚ (v.adicCompletion ℚ) (1 / 2) = 1 by
        rw [show (2 : v.adicCompletion ℚ) = algebraMap ℚ _ 2 from (map_ofNat _ 2).symm, ← map_mul]; norm_num, map_one]
    refine le_antisymm hle ?_
    calc (1 : _) = _ := hprod.symm
      _ ≤ Valued.v (2 : v.adicCompletion ℚ) * 1 := mul_le_mul' le_rfl hle'
      _ = _ := mul_one _
  · rw [Algebra.TensorProduct.one_def]; exact hint 1 (fun k => hlv (0, k))
  · intro y z hy hz k

    rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_

    rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · intro y z hy hz k

    rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_

    rw [map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' (mul_le_mul' ((hmem _).1 (hy i)) le_rfl) ((hmem _).1 (hcv (i, j, k))))
      (by simpa using hz j)
  · intro y hy k

    rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))
  · intro y hy k

    rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' le_rfl ((hmem _).1 (hsv (i, k)))) (by simpa using hy i)

theorem unit_fixed_is_norm : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  intro L _ _ c hc hne κ bL
  obtain ⟨x, hx⟩ := hne
  set θ : L := x - c x with hθdef
  have hθ : θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcθ : c θ = -θ := by simp [θ, hc]
  obtain ⟨S, hS⟩ := good_eventually L c κ bL θ
  refine ⟨S, fun v hv e hee hei hei' => ?_⟩
  obtain ⟨h2, h1, hmul, hmulS, hσI, hσS, hθI, hθI'⟩ := hS v hv
  set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r l => simp [σ, hc]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hσinv : ∀ g : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, σ ↑g = ↑g → σ ↑g⁻¹ = ↑g⁻¹ := by
    intro g hg
    calc σ ↑g⁻¹ = σ ↑g⁻¹ * (↑g * ↑g⁻¹) := by simp
      _ = σ (↑g⁻¹ * ↑g) * ↑g⁻¹ := by rw [map_mul, hg]; ring
      _ = ↑g⁻¹ := by simp
  let θu : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    ⟨1 ⊗ₜ θ, 1 ⊗ₜ θ⁻¹,
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hθ, Algebra.TensorProduct.one_def],
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hθ, Algebra.TensorProduct.one_def]⟩
  have hσθ : σ ↑θu = -↑θu := by simp [θu, σ, hcθ, TensorProduct.tmul_neg]
  obtain ⟨z, hzI, hzS⟩ := GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor v L c hc κ bL h2 h1 hmul hmulS hσI θu hθI hθI' hσθ e hee hei hei'
  set w := z * σ z with hwdef
  have hwσ : σ w = w := by simp only [w, map_mul, hσσ]; ring
  set u : v.adicCompletion ℚ ⊗[ℚ] L := ↑e⁻¹ * w with hudef
  have huI : IsIntB v bL u := hmul _ _ hei' (hmul _ _ hzI (hσI _ hzI))
  have huS : IsSmallB v bL (u - 1) := by
    have : u - 1 = ↑e⁻¹ * (w - ↑e) := by simp [u, mul_sub]
    rw [this]; exact hmulS _ _ hei' hzS
  obtain ⟨f, hfI, hfI', hf2, hfS, huniq⟩ := GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt v L κ bL h2 h1 hmul hmulS u huI huS
  have hσu : σ u = u := by simp only [u, map_mul, hσinv e hee, hwσ]
  have hσf : σ ↑f = ↑f := by
    refine huniq _ (hσI _ hfI) (by rw [← map_pow, hf2, hσu]) ?_
    have := hσS _ hfS
    simpa using this
  have hw : w = ↑e * ↑f ^ 2 := by rw [hf2]; simp [u]
  have hzU : IsUnit z := isUnit_of_mul_isUnit_left (x := z) (y := σ z)
    (by rw [← hwdef, hw]; exact e.isUnit.mul (f.isUnit.pow 2))
  obtain ⟨zu, hzu⟩ := hzU
  refine ⟨zu * f⁻¹, ?_⟩
  have hf' := hσinv f hσf
  simp only [Units.val_mul, map_mul, hf', hzu]
  have : (↑e : v.adicCompletion ℚ ⊗[ℚ] L) = w * ↑f⁻¹ * ↑f⁻¹ := by
    rw [hw]; simp [pow_two, mul_assoc]
  rw [this, hwdef]; ring

end GlobalTheory.LocNorm
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_one_mul_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type)
    (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  intro A _ _ _ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ k : κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr 1 k) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun k => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and h1)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, h1v⟩ := hv
  refine ⟨fun k => ?_, fun y z hy hz k => ?_⟩
  · rw [Algebra.TensorProduct.one_def, repr_tmul_apply, one_mul]
    exact h1v k
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
      refine sum_mem fun i _ => ?_
      rw [map_sum, Finsupp.finsetSum_apply]
      refine sum_mem fun j _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
      exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))

end GlobalTheory.AdicSpan
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem GlobalTheory.PtDeg.intFrame_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) ∧ ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV
  intro yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL
  exact ⟨GlobalTheory.T.cm_point_integral_frame_mem_span_eigen_lattice E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL,
    GlobalTheory.T.completed_eigenLattice_le_span_integral_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL⟩
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

theorem _root_.GlobalTheory.T.integrable_zeta_integral_matrix_schwartz : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (haarVol (KO k (Fin n))) := by
  first | exact @GlobalTheory.GJIntegrable.integrable_gjIntegrand | exact GlobalTheory.GJIntegrable.integrable_gjIntegrand | (intros; apply GlobalTheory.GJIntegrable.integrable_gjIntegrand <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

theorem _root_.GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsNbhd B A' f → ∀ (m i : ℤ), 2 ≤ m → ∀ z : Ht q (sp (Localization.Away (algebraMap B A' f))) m i, ∃ (A'' : Type) (_ : CommRing A'') (_ : Algebra B A'') (_ : Algebra.Etale B A'') (φ : A' →ₐ[B] A''), IsNbhd B A'' f ∧ pull _ (spMap (awayHom φ f)) _ _ z = 0 := by
  first | (exact @GlobalTheory.KillFiner.main) | (exact GlobalTheory.KillFiner.main) | (intros; apply GlobalTheory.KillFiner.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) : Set (GlobalTheory.LeviDesc.parP a n w)) (((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) : Subgroup _) : Set (GlobalTheory.LeviDesc.parP a n w)) | GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (((Quotient.out d)⁻¹ * ⟨blk h w m 0, hγ⟩ * Quotient.out d : GlobalTheory.LeviDesc.parP a n w) : GLw n w) ≠ 0}.Finite := by
  first | exact @GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets | exact GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets | (intros; apply GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets <;> assumption)
end
