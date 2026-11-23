module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle001
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.CongruenceExistence

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem memK {w : Plc L} (h : GL (Fin n) (Kw w)) : h ∈ GlobalTheory.LFun.KGL w (n := n) ↔
    (∀ i j, h.1 i j ∈ w.adicCompletionIntegers L) ∧ ∀ i j, (h⁻¹).1 i j ∈ w.adicCompletionIntegers L := by
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]; rfl

private theorem memO {x : Af L} : x ∈ UpperTheory.V.Af.Ohat L ↔ ∀ w : Plc L, pLoc L w x ∈ w.adicCompletionIntegers L := by
  rw [UpperTheory.V.Af.Ohat, Subring.mem_iInf]; rfl

private def fp : UA L n →* GL (Fin n) (Af L) :=
  (Matrix.GeneralLinearGroup.map (pFin L)).comp (UA L n).subtype

private theorem cLoc_val (w : Plc L) (x : UA L n) (i j : Fin n) :
    (cLoc w x).1 i j = pLoc L w ((fp x).1 i j) := rfl

private theorem cLoc_inv_val (w : Plc L) (x : UA L n) (i j : Fin n) :
    ((cLoc w x)⁻¹).1 i j = pLoc L w (((fp x)⁻¹).1 i j) := by
  rw [← map_inv, ← map_inv]; rfl

private theorem pLoc_one (w : Plc L) (i j : Fin n) :
    pLoc L w ((1 : Matrix (Fin n) (Fin n) (Af L)) i j) = (1 : Matrix (Fin n) (Fin n) (Kw w)) i j := by
  simp only [Matrix.one_apply]; split_ifs <;> simp

private theorem mem_iff {m : ℕ} (hm : m ≠ 0) (x : UA L n) :
    (x ∈ finU (E := L) (n := n) ∧ fp x ∈ UpperTheory.V.Af.KLev L n m) ↔
      x ∈ Kall L n ∧ ∀ w i j, ∃ a ∈ w.adicCompletionIntegers L, (mL w x - 1) i j = (m : Kw w) * a := by
  have hd : ∀ (w : Plc L) (i j : Fin n), (mL w x - 1) i j =
      pLoc L w ((fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j) := fun w i j => by
    rw [map_sub, pLoc_one, Matrix.sub_apply]; rfl
  constructor
  · rintro ⟨hf, hk⟩
    obtain ⟨h1, h2, h3⟩ := UpperTheory.V.Af.mem_KLev.1 hk
    refine ⟨⟨hf, Subgroup.mem_iInf.2 fun w => (memK _).2 ⟨fun i j => ?_, fun i j => ?_⟩⟩, fun w i j => ?_⟩
    · rw [cLoc_val]; exact memO.1 (h1 i j) w
    · rw [cLoc_inv_val]; exact memO.1 (h2 i j) w
    · obtain ⟨y, hy, e⟩ := h3 i j
      refine ⟨pLoc L w y, memO.1 hy w, ?_⟩
      rw [hd, show (fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j = (m : Af L) * y from e, map_mul, map_natCast]
  · rintro ⟨⟨hf, hK⟩, hc⟩
    have hK' : ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) := fun w => Subgroup.mem_iInf.1 hK w
    have hm' : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm
    set u : Af L := algebraMap L (Af L) (m : L)⁻¹ with hu'
    have hu : u * (m : Af L) = 1 := by
      rw [hu', ← map_natCast (algebraMap L (Af L)), ← map_mul, inv_mul_cancel₀ hm', map_one]
    refine ⟨hf, UpperTheory.V.Af.mem_KLev.2 ⟨fun i j => memO.2 fun w => ?_, fun i j => memO.2 fun w => ?_, fun i j =>
      ⟨u * ((fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j), memO.2 fun w => ?_, ?_⟩⟩⟩
    · rw [← cLoc_val]; exact ((memK _).1 (hK' w)).1 i j
    · rw [← cLoc_inv_val]; exact ((memK _).1 (hK' w)).2 i j
    · obtain ⟨a, ha, e⟩ := hc w i j
      rw [map_mul, ← hd, e, ← mul_assoc]
      have : pLoc L w u * (m : Kw w) = 1 := by
        have := congrArg (pLoc L w) hu
        rwa [map_mul, map_natCast, map_one] at this
      rwa [this, one_mul]
    · rw [← mul_assoc, mul_comm _ u, hu, one_mul]

private def cong (m : ℕ) : Subgroup (UA L n) := finU (E := L) (n := n) ⊓ (UpperTheory.V.Af.KLev L n m).comap fp

private theorem isCong {m : ℕ} (hm : m ≠ 0) : IsCong m (cong (L := L) (n := n) m) := fun x => mem_iff hm x

private theorem isLevel {m : ℕ} (hm : m ≠ 0) : IsLevel (cong (L := L) (n := n) m) := by
  refine ⟨fun x hx => ((isCong hm x).1 hx).1, ?_⟩
  have hc : Continuous fun x : finU (E := L) (n := n) => fp (x : UA L n) :=
    GlobalTheory.CuspRep.continuous_mapFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  convert (UpperTheory.V.Af.isOpen_KLev (F := L) (n := n) (M := m) (Nat.one_le_iff_ne_zero.2 hm)).preimage hc using 1
  ext x
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

private theorem trans_int {w : Plc L} {i j : Fin n} {c : Kw w} (hc : c ∈ w.adicCompletionIntegers L) (a b : Fin n) :
    Matrix.transvection i j c a b ∈ w.adicCompletionIntegers L := by
  rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  refine add_mem ?_ ?_
  · split_ifs
    · exact one_mem _
    · exact zero_mem _
  · split_ifs
    · exact hc
    · exact zero_mem _

private def el {w : Plc L} {i j : Fin n} (h : i ≠ j) : GL (Fin n) (Kw w) :=
  ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

private theorem el_mem {w : Plc L} {i j : Fin n} (h : i ≠ j) : el (w := w) h ∈ GlobalTheory.LFun.KGL w (n := n) :=
  (memK _).2 ⟨fun a b => trans_int (one_mem _) a b, fun a b => trans_int (neg_mem (one_mem _)) a b⟩

private theorem last {m : ℕ} (hn : 2 ≤ n) (w : Plc L) (hw : IsSplitAt w)
    (hle : locU n w ⊓ Kall L n ≤ cong (L := L) (n := n) m) (hm : m ≠ 0) : (m : 𝓞 L) ∉ w.asIdeal := by
  intro hmw
  obtain ⟨h1, -, -, -, -, -, -, h8⟩ := UpperTheory.V.Z.Sym.Dict.Br.uaFacts L n
  obtain ⟨hl, hc, -, -⟩ := h1 w hw
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set g : GL (Fin n) (Kw w) := el hij with hg
  have hx := hl g
  have hK : secW n w g ∈ Kall L n := by
    refine ⟨hx.1, Subgroup.mem_iInf.2 fun u => ?_⟩
    by_cases hu : un u = un w
    · refine h8 w hw _ ?_ u hu
      rw [hc]; exact el_mem hij
    · have : secW n w g ∈ (cLoc (E := L) (n := n) u).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 u) hu
      exact Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 this]; exact one_mem _)
  obtain ⟨a, ha, e⟩ := ((isCong hm _).1 (hle ⟨hx, hK⟩)).2 w ⟨0, by omega⟩ ⟨1, by omega⟩
  have e1 : (mL w (secW n w g) - 1) ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
    rw [mL, hc]
    simp [g, el, Matrix.transvection, Matrix.single_apply]
  rw [e1] at e
  have hv : Valued.v ((m : Kw w)) < 1 := by
    have h0 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w (m : 𝓞 L)).2 hmw
    have e2 : (m : Kw w) = algebraMap L (Kw w) (algebraMap (𝓞 L) L (m : 𝓞 L)) := by simp
    rw [e2]
    first
      | (rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact h0)
      | (rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact h0)
      | (erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact h0)
  have ha' : Valued.v a ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ha
  have := congrArg Valued.v e
  rw [map_one, map_mul] at this
  have h3 : Valued.v (m : Kw w) * Valued.v a < 1 := by
    calc _ ≤ Valued.v (m : Kw w) * 1 := by gcongr
      _ < 1 := by simpa using hv
  exact absurd this h3.ne'

end UpperTheory.V.Z.Sym.So.CongruenceExistence

open UpperTheory.V.Z.Sym.So.CongruenceExistence in
theorem UpperTheory.V.Z.Sym.So.congEx :
    UpperTheory.V.Z.Sym.So.CongEx := by
  intro L _ _ _ n m hm
  exact ⟨cong m, isCong hm, isLevel hm, fun hn w hw hle => last hn w hw hle hm⟩

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.So.dcAt :
    UpperTheory.V.Z.Sym.So.DcAt := by
  intro L _ _ _ n U₀ S VL hP w hw hF d
  obtain ⟨hsec, hcomm, -, -, -, -, hcomp, hK⟩ := UpperTheory.V.Z.Sym.Dict.Br.uaFacts L n
  have hsp : IsSplitAt w := hP.split w hw
  obtain ⟨hloc, hcl, -, hsecx⟩ := hsec w hsp
  obtain ⟨-, -, -, -, -, hfin⟩ := UpperTheory.V.Z.Sym.Sig.finFacts (Kw w) (VL w)
  obtain ⟨hH, -, -, hJK⟩ := hfin n
  have hKO : GlobalTheory.SplitWeil.KO (Kw w) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  have hoff : ∀ (h : GL (Fin n) (Kw w)) (u : Plc L), un u ≠ un w → cLoc u (secW n w h) = 1 := fun h u e =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (hloc h).2 u) e
  have h2 : ∀ u ∈ lev U₀ S VL, cLoc w u ∈ (VL w).J n ∧ ∀ h, u * (secW n w (cLoc w u))⁻¹ * secW n w h =
      secW n w h * (u * (secW n w (cLoc w u))⁻¹) := fun u hu => by
    refine ⟨Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu.2 w) hw, fun h => ?_⟩
    obtain ⟨a, ha, hau⟩ := hcomp w u (hF.1 hu.1).1
    have ea : secW n w (cLoc w u) = a := by rw [← hau w rfl, ← hsecx a ha]
    have hy : ∀ u', un u' = un w → cLoc u' (u * (secW n w (cLoc w u))⁻¹) = 1 := fun u' e => by
      rw [map_mul, map_inv, ea, hau u' e, mul_inv_cancel]
    exact (hcomm w _ (hloc h) _ hy).symm.eq
  have h3 : ∀ h ∈ (VL w).J n, secW n w h ∈ lev U₀ S VL := fun h hh => by
    refine ⟨hF.2 w (Finset.mem_singleton_self w) ⟨hloc h, ⟨(hloc h).1, Subgroup.mem_iInf.2 fun u => ?_⟩⟩, ?_⟩
    · by_cases e : un u = un w
      · refine hK w hsp _ ?_ u e
        rw [hcl, ← hKO]
        exact hJK hh
      · rw [Subgroup.mem_comap, hoff h u e]
        exact one_mem _
    · refine Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_
      by_cases e : w' = w
      · subst e
        rw [Subgroup.mem_comap, hcl]
        exact hh
      · rw [Subgroup.mem_comap, hoff h w' fun e' => e (hP.inj hw' hw e')]
        exact one_mem _
  have main := fun (V : Type) [AddCommGroup V] [Module ℂ V] =>
    UpperTheory.V.Z.Sym.So.dcLocal _ _ V (secW n w) (cLoc w) ((VL w).J n) (lev U₀ S VL) hcl h2 h3 (Sig.dg d) (hH _)
  refine ⟨(main ℂ).1, fun V _ _ φ hφ c => ?_⟩
  unfold EigAt
  rw [(main V).2 φ hφ]

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem dc_right (U : Subgroup G) (a : G) {r s : G} (h : r⁻¹ * s ∈ U) (hr : r ∈ DC U a) :
    s ∈ DC U a := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hr
  refine ⟨u, hu, w * ((u * a * w)⁻¹ * s), U.mul_mem hw h, ?_⟩
  group

private theorem dc_left (U : Subgroup G) (b : G) {c g : G} (h : c ∈ U) (hg : g ∈ DC U b) :
    c * g ∈ DC U b := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hg
  exact ⟨c * u, U.mul_mem h hu, w, hw, by group⟩

private theorem out_inv_mul_mem (U : Subgroup G) (s : G) :
    (Quotient.out (s : G ⧸ U))⁻¹ * s ∈ U :=
  QuotientGroup.eq.1 (QuotientGroup.out_eq' (s : G ⧸ U))

private theorem uf_unique_iff (U : Subgroup G) (a b g : G) :
    (∃! y : G ⧸ U, y.out ∈ DC U a ∧ y.out⁻¹ * g ∈ DC U b) ↔
      ∃ r, (r ∈ DC U a ∧ r⁻¹ * g ∈ DC U b) ∧
        ∀ s, s ∈ DC U a → s⁻¹ * g ∈ DC U b → r⁻¹ * s ∈ U := by
  have hq : ∀ s, s ∈ DC U a → s⁻¹ * g ∈ DC U b →
      (Quotient.out (s : G ⧸ U)) ∈ DC U a ∧ (Quotient.out (s : G ⧸ U))⁻¹ * g ∈ DC U b := by
    intro s hs hs'
    have h1 := out_inv_mul_mem U s
    have h2 : s⁻¹ * Quotient.out (s : G ⧸ U) ∈ U := by
      have := U.inv_mem h1
      simpa using this
    refine ⟨dc_right U a h2 hs, ?_⟩
    have := dc_left U b h1 hs'
    simpa [mul_assoc] using this
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, huniq⟩
    refine ⟨y.out, ⟨hy1, hy2⟩, fun s hs hs' => ?_⟩
    have h3 : (s : G ⧸ U) = y := huniq _ (hq s hs hs')
    have h4 : ((y.out : G) : G ⧸ U) = (s : G ⧸ U) := by
      rw [h3]; exact QuotientGroup.out_eq' y
    exact QuotientGroup.eq.1 h4
  · rintro ⟨r, ⟨hr1, hr2⟩, hall⟩
    refine ⟨(r : G ⧸ U), hq r hr1 hr2, fun y hy => ?_⟩
    have h5 := hall _ hy.1 hy.2
    have h6 : (r : G ⧸ U) = ((y.out : G) : G ⧸ U) := QuotientGroup.eq.2 h5
    rw [h6]
    exact (QuotientGroup.out_eq' y).symm

private theorem reps_of_finOrb (U : Subgroup G) (a : G) (h : AlgebraTools.FinOrb U U a) :
    ∃ R : Finset G, (∀ y ∈ R, y ∈ DC U a) ∧ (∀ y ∈ DC U a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U) := by
  classical
  have hf : (MulAction.orbit U (a : G ⧸ U)).Finite := h
  have hmk : ∀ y ∈ DC U a, (y : G ⧸ U) ∈ MulAction.orbit U (a : G ⧸ U) := by
    rintro y ⟨u, hu, w, hw, rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    show ((u * a : G) : G ⧸ U) = ((u * a * w : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    simpa [mul_assoc] using hw
  refine ⟨hf.toFinset.image (fun q : G ⧸ U => q.out), ?_, ?_⟩
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨u, rfl⟩ := hf.mem_toFinset.1 hq
    have h1 : ((Quotient.out (u • (a : G ⧸ U)) : G) : G ⧸ U) = ((u * a : G) : G ⧸ U) :=
      QuotientGroup.out_eq' _
    have h2 := QuotientGroup.eq.1 h1
    refine ⟨u, u.2, _, U.inv_mem h2, ?_⟩
    group
  · intro y hy
    refine ⟨Quotient.out (y : G ⧸ U), ⟨?_, out_inv_mul_mem U y⟩, ?_⟩
    · exact Finset.mem_image.2 ⟨_, hf.mem_toFinset.2 (hmk y hy), rfl⟩
    · rintro r ⟨hr, hr'⟩
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hr
      have h3 : ((q.out : G) : G ⧸ U) = (y : G ⧸ U) := QuotientGroup.eq.2 hr'
      have h4 : q = (y : G ⧸ U) := (QuotientGroup.out_eq' q).symm.trans h3
      rw [h4]

private theorem finOrb_of_cover (U : Subgroup G) (a : G) (R : Finset G)
    (h : ∀ y ∈ DC U a, ∃ r ∈ R, r⁻¹ * y ∈ U) : AlgebraTools.FinOrb U U a := by
  classical
  refine (R.image (fun r : G => (r : G ⧸ U))).finite_toSet.subset ?_
  rintro q ⟨u, rfl⟩
  obtain ⟨r, hr, hr'⟩ := h ((u : G) * a) ⟨u, u.2, 1, U.one_mem, by simp⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨r, hr, ?_⟩)
  exact QuotientGroup.eq.2 hr'

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcMap :
    UpperTheory.V.Z.Sym.So.DcMap := by
  classical
  intro G G' V _ _ _ _ e he U' a b
  set U := U'.comap e with hU
  set inv : G' → G := Function.surjInv he.2 with hinv
  have einv : ∀ x, e (inv x) = x := Function.surjInv_eq he.2
  have hDC : ∀ c g : G, g ∈ DC U c ↔ e g ∈ DC U' (e c) := by
    intro c g
    constructor
    · rintro ⟨u, hu, w, hw, rfl⟩
      exact ⟨e u, hu, e w, hw, by simp⟩
    · rintro ⟨u, hu, w, hw, h⟩
      refine ⟨inv u, ?_, inv w, ?_, he.1 ?_⟩
      · show e (inv u) ∈ U'
        rwa [einv]
      · show e (inv w) ∈ U'
        rwa [einv]
      · simp [einv, h]
  have hmem : ∀ x y : G, x⁻¹ * y ∈ U ↔ (e x)⁻¹ * e y ∈ U' := by
    intro x y
    show e (x⁻¹ * y) ∈ U' ↔ _
    simp
  have hfin : AlgebraTools.FinOrb U U a ↔ AlgebraTools.FinOrb U' U' (e a) := by
    constructor
    · intro h
      obtain ⟨R, -, hR⟩ := reps_of_finOrb U a h
      refine finOrb_of_cover U' (e a) (R.image e) fun y' hy' => ?_
      have hy : inv y' ∈ DC U a := (hDC a _).2 (by rwa [einv])
      obtain ⟨r, ⟨hr, hr'⟩, -⟩ := hR _ hy
      refine ⟨e r, Finset.mem_image_of_mem _ hr, ?_⟩
      have := (hmem _ _).1 hr'
      rwa [einv] at this
    · intro h
      obtain ⟨R, -, hR⟩ := reps_of_finOrb U' (e a) h
      refine finOrb_of_cover U a (R.image inv) fun y hy => ?_
      obtain ⟨r, ⟨hr, hr'⟩, -⟩ := hR _ ((hDC a y).1 hy)
      refine ⟨inv r, Finset.mem_image_of_mem _ hr, (hmem _ _).2 ?_⟩
      rwa [einv]
  refine ⟨hDC a, hfin, ?_, ?_⟩
  · have hQ : ∀ g : G, (∃! y : G ⧸ U, y.out ∈ DC U a ∧ y.out⁻¹ * g ∈ DC U b) ↔
        ∃! y : G' ⧸ U', y.out ∈ DC U' (e a) ∧ y.out⁻¹ * e g ∈ DC U' (e b) := by
      intro g
      rw [uf_unique_iff, uf_unique_iff]
      have hin : ∀ (r : G), (r ∈ DC U a ∧ r⁻¹ * g ∈ DC U b) ↔
          (e r ∈ DC U' (e a) ∧ (e r)⁻¹ * e g ∈ DC U' (e b)) := by
        intro r
        rw [hDC a r, hDC b (r⁻¹ * g)]
        simp
      constructor
      · rintro ⟨r, hr, hall⟩
        refine ⟨e r, (hin r).1 hr, fun s' h1 h2 => ?_⟩
        have h3 := (hin (inv s')).2 (by rw [einv]; exact ⟨h1, h2⟩)
        have := (hmem _ _).1 (hall _ h3.1 h3.2)
        rwa [einv] at this
      · rintro ⟨r', hr', hall⟩
        have h0 := (hin (inv r')).2 (by rw [einv]; exact hr')
        refine ⟨inv r', h0, fun s h1 h2 => (hmem _ _).2 ?_⟩
        have h3 := (hin s).1 ⟨h1, h2⟩
        rw [einv]
        exact hall _ h3.1 h3.2
    have hR : ∀ g y : G, (y ∈ DC U a → y⁻¹ * g ∈ DC U b → g ∈ DC U (a * b)) ↔
        (e y ∈ DC U' (e a) → (e y)⁻¹ * e g ∈ DC U' (e b) → e g ∈ DC U' (e a * e b)) := by
      intro g y
      rw [hDC a y, hDC b (y⁻¹ * g), hDC (a * b) g]
      simp
    constructor
    · intro h g'
      have hg : e (inv g') = g' := einv g'
      obtain ⟨h1, h2⟩ := h (inv g')
      rw [← hg]
      refine ⟨fun hm => (hQ _).1 (h1 ((hDC _ _).2 (by simpa using hm))), fun y' hy1 hy2 => ?_⟩
      have := (hR (inv g') (inv y')).1 (h2 _)
      rw [einv] at this
      exact this hy1 hy2
    · intro h g
      obtain ⟨h1, h2⟩ := h (e g)
      refine ⟨fun hm => (hQ g).2 (h1 (by simpa using (hDC _ _).1 hm)), fun y hy1 hy2 => ?_⟩
      exact (hR g y).2 (h2 (e y)) hy1 hy2
  · intro hf φ hφ
    obtain ⟨R', hR1', hR2'⟩ := reps_of_finOrb U' (e a) hf
    have hφe : ∀ u ∈ U, ∀ g, (φ ∘ e) (g * u) = (φ ∘ e) g := by
      intro u hu g
      simp only [Function.comp_apply, map_mul]
      exact hφ _ hu _
    have hinj : Set.InjOn inv (R' : Set G') := fun x _ y _ h => by
      rw [← einv x, ← einv y, h]
    have hR1 : ∀ y ∈ R'.image inv, y ∈ DC U a := by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      exact (hDC a _).2 (by rw [einv]; exact hR1' r hr)
    have hR2 : ∀ y ∈ DC U a, ∃! r, r ∈ R'.image inv ∧ r⁻¹ * y ∈ U := by
      intro y hy
      obtain ⟨r, ⟨hr, hr'⟩, huniq⟩ := hR2' _ ((hDC a y).1 hy)
      refine ⟨inv r, ⟨Finset.mem_image_of_mem _ hr, (hmem _ _).2 (by rwa [einv])⟩, ?_⟩
      rintro s ⟨hs, hs'⟩
      obtain ⟨s', hs1, rfl⟩ := Finset.mem_image.1 hs
      have := (hmem _ _).1 hs'
      rw [einv] at this
      rw [huniq s' ⟨hs1, this⟩]
    funext g
    rw [(dcBasic G V U a (hfin.2 hf) (φ ∘ e) hφe).2.2.2.2 _ hR1 hR2 g, Function.comp_apply,
      (dcBasic G' V U' (e a) hf φ hφ).2.2.2.2 R' hR1' hR2' (e g), Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [einv]

end
end
