module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle033
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle194
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle193
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle038
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle157
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.TotallySplit
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
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_intUnitary_of_gramClass : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q n n' JS JT hU hq hJS hJT hS hT x y _hG hA hGr hidx
  classical
  have hvϖ := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖint : ϖ ∈ Formalism.UG.intL L := by
    unfold Formalism.UG.intL
    rw [Valuation.mem_integer_iff, hvϖ]
    exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by decide)
  have mulVec_int : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) L) (v : Fin b → L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ j, v j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ v) i ∈ Formalism.UG.intL L := by
    intro a b M v hM hv i
    simp only [Matrix.mulVec, dotProduct]
    exact (Formalism.UG.intL L).sum_mem fun j _ => (Formalism.UG.intL L).mul_mem (hM i j) (hv j)
  obtain ⟨V, hV, a, hxV⟩ := GlobalTheory.T.exists_elementaryDivisors_integral_preimage_lattice L ϖ hvϖ n n' x
  obtain ⟨g0, hg0⟩ := hV
  have hVint : ∀ i j, (V : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  have hVinv : ∀ i j, ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (Formalism.UG.intL L)) : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  set Vm : Matrix (Fin n) (Fin n) L := (V : Matrix (Fin n) (Fin n) L) with hVm
  have hyV : ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (y *ᵥ (Vm *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
    intro c hc
    have hu : ∀ i, (Vm *ᵥ c) i ∈ Formalism.UG.intL L := mulVec_int Vm c hVint hc
    rw [← hxV c hc]
    exact ⟨fun h => GlobalTheory.T.latticeKernel_le_of_matrixLatticeIndex_eq L ϖ σ q hU n n' x y hA.1 hidx _ hu h, fun h => hA.1 _ hu h⟩
  let ej : Fin n → Fin n → L := fun j => Pi.single j (ϖ ^ a j)
  have hej_int : ∀ j k, ej j k ∈ Formalism.UG.intL L := by
    intro j k
    by_cases h : k = j
    · subst h; simpa [ej] using (Formalism.UG.intL L).pow_mem hϖint (a k)
    · simp [ej, Pi.single_apply, h]
  have hej_dvd : ∀ j k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a k) (ej j k) := by
    intro j k
    by_cases h : k = j
    · subst h; exact ⟨1, (Formalism.UG.intL L).one_mem, by simp [ej]⟩
    · simpa [ej, Pi.single_apply, h] using GlobalTheory.Hk3.IntWitt.dvdPow_zero ϖ (a k)
  let zx : {j : Fin n // 0 < a j} → Fin n' → L := fun j => x *ᵥ (Vm *ᵥ ej j)
  let zy : {j : Fin n // 0 < a j} → Fin n' → L := fun j => y *ᵥ (Vm *ᵥ ej j)
  have hzx : ∀ j r, zx j r ∈ Formalism.UG.intL L := fun j => (hxV _ (hej_int j)).mpr (hej_dvd j)
  have hzy : ∀ j r, zy j r ∈ Formalism.UG.intL L := fun j => (hyV _ (hej_int j)).mpr (hej_dvd j)
  have hix : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zx := GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer L ϖ hvϖ n n' x Vm a hxV
  have hiy : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zy := GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer L ϖ hvϖ n n' y Vm a hyV
  have hgr := GlobalTheory.T.gramClass_elementaryDivisor_columns_congr L ϖ σ q hU n n' JT x y Vm a hVint hxV hGr
  obtain ⟨h, hh, hcong⟩ := GlobalTheory.T.integralWittTheorem_mod_uniformizerPow L ϖ σ q hU hq n' JT hJT hT {j : Fin n // 0 < a j} (fun j => a j) zx zy
    (fun j => j.2) hzx hzy hix hiy (fun i j => hgr i j)
  refine ⟨h, hh, ?_⟩
  set H : Matrix (Fin n') (Fin n') L := ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hH
  have hHint : ∀ i j, H i j ∈ Formalism.UG.intL L := by
    obtain ⟨h0, hh0⟩ := hh
    intro i j; rw [hH, ← hh0]; exact ((h0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2
  set M := y - H * x with hM
  have hMv : ∀ w : Fin n → L, M *ᵥ w = y *ᵥ w - H *ᵥ (x *ᵥ w) := by
    intro w; rw [hM, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  have hcol : ∀ j i, (M *ᵥ (Vm *ᵥ Pi.single j 1)) i ∈ Formalism.UG.intL L := by
    intro j i
    by_cases ha : a j = 0
    · have he : Pi.single j (1 : L) = ej j := by simp [ej, ha]
      rw [he, hMv]
      exact (Formalism.UG.intL L).sub_mem ((hyV _ (hej_int j)).mpr (hej_dvd j) i)
        (mulVec_int H _ hHint ((hxV _ (hej_int j)).mpr (hej_dvd j)) i)
    · have hpos : 0 < a j := Nat.pos_of_ne_zero ha
      obtain ⟨b, hb, hbe⟩ := hcong ⟨j, hpos⟩ i
      have he : ej j = ϖ ^ a j • Pi.single j (1 : L) := by
        funext k; simp [ej, Pi.single_apply]
      have key : ϖ ^ a j * (M *ᵥ (Vm *ᵥ Pi.single j 1)) i = ϖ ^ a j * (-b) := by
        have : (M *ᵥ (Vm *ᵥ ej j)) i = -((H *ᵥ zx ⟨j, hpos⟩) i - zy ⟨j, hpos⟩ i) := by
          rw [hMv]; simp only [zx, zy, Pi.sub_apply]; ring
        rw [he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at this
        rw [this, hbe]; ring
      have := mul_left_cancel₀ (pow_ne_zero _ hϖ0) key
      rw [this]; exact (Formalism.UG.intL L).neg_mem hb
  intro i r
  have hMe : M = (M * Vm) * ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.mul_assoc, hVm, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hMe, Matrix.mul_apply]
  refine (Formalism.UG.intL L).sum_mem fun k _ => (Formalism.UG.intL L).mul_mem ?_ (hVinv k r)
  have hc := hcol k i
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at hc

end GlobalTheory.Hk3.HoweG

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitChart

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

def sc (he : SplitAt D v e) (z : AE D) : Fv D.host.F v := (he.exists_scalar z).choose

theorem sc_spec (he : SplitAt D v e) (z : AE D) : e * z = fj D (singleV D.host.F v (sc he z)) * e :=
  (he.exists_scalar z).choose_spec

theorem sc_eq (he : SplitAt D v e) {z : AE D} {α : Af D.host.F} (h : e * z = fj D α * e) :
    sc he z = evalV D.host.F v α := by
  rw [sc_spec he] at h
  rw [← he.scalar_inj h, evalV_singleV_same]

def comp (he : SplitAt D v e) : AE D →+* Fv D.host.F v where
  toFun := sc he
  map_one' := by rw [sc_eq he (α := 1) (by rw [he.one_mul', mul_one]), map_one]
  map_zero' := by rw [sc_eq he (α := 0) (by rw [map_zero, mul_zero, zero_mul]), map_zero]
  map_mul' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) * singleV D.host.F v (sc he y)), map_mul,
      evalV_singleV_same, evalV_singleV_same]
    rw [map_mul]
    linear_combination y * sc_spec he x + fj D (singleV D.host.F v (sc he x)) * sc_spec he y
  map_add' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) + singleV D.host.F v (sc he y)), map_add (f := _),
      evalV_singleV_same, evalV_singleV_same]
    rw [map_add (f := _)]
    linear_combination sc_spec he x + sc_spec he y

theorem comp_apply (he : SplitAt D v e) (z : AE D) : comp he z = sc he z := rfl

theorem comp_fj (he : SplitAt D v e) (α : Af D.host.F) : comp he (fj D α) = evalV D.host.F v α :=
  sc_eq he (mul_comm _ _)

theorem comp_self (he : SplitAt D v e) : comp he e = 1 := by
  rw [comp_apply, sc_eq he (α := 1) (by rw [he.one_mul', he.1]), map_one]

theorem comp_algebraMap (he : SplitAt D v e) (y : AF D.host.F) :
    comp he (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v y.2 := by
  rw [comp_apply, sc_eq he (α := y.2 * 1), mul_one]
  rw [← algebraMap_mul_fj, mul_assoc, he.one_mul', mul_comm]

theorem isIntegral_of_int (O : Type) {K L : Type} [CommRing O] [CommRing K] [CommRing L] [Algebra O K]
    (f : L →+* K) {x : L} (hx : IsIntegral ℤ x) : IsIntegral O (f x) :=
  (map_isIntegral_int f hx).tower_top

theorem comp_mem (he : SplitAt D v e) {z : AE D} (hz : z ∈ intL D) :
    comp he z ∈ v.adicCompletionIntegers D.host.F := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    have h1 : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E) : AE D) =
        fj D α * (1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) := by
      show _ = (_ ⊗ₜ _) * _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h1, map_mul, comp_fj]
    refine mul_mem (hα v) ?_
    have h3 : IsIntegral (v.adicCompletionIntegers D.host.F)
        (comp he ((1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E))) :=
      isIntegral_of_int _ ((comp he).comp
        (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toRingHom) o.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
    rw [← hy]
    exact y.2
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (comp he)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_mem {z : AE D} (hz : z ∈ intL D) : finPart D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem chart_comp (he : SplitAt D v e) : Chart e v (comp he) := by
  refine ⟨fun a => ⟨fj D (singleV D.host.F v a), by rw [comp_fj, evalV_singleV_same]⟩, fun a => ⟨fun h => ?_, fun h => ?_⟩,
    comp_algebraMap he, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    rw [sc_spec he, ← comp_apply, h, h0, map_zero, zero_mul]
  · rw [← one_mul (comp he a), ← comp_self he, ← map_mul, h, map_zero]
  · have h1 := comp_mem he (inF_mem h)
    rw [inF_finPart, ← mul_assoc, he.one_mul', map_mul, comp_self, one_mul] at h1
    exact isInt_Ov.2 h1
  · rw [sc_spec he]
    exact finPart_mem (fj_mul_mem (singleV_mem_intAf D.host.F v ⟨_, isInt_Ov.1 h⟩) he.mem)

theorem exists_chart : ∀ {D : D7} (e : AE D), IsSplitIdem D e →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), Chart e v π := by
  intro D e h
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h
  exact ⟨v, comp he, chart_comp he⟩

end GlobalTheory.SplitChart

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitExist

theorem dv_of_conj {R : Type} [CommRing R] {n : ℕ} {Λ : (Fin n → R) → Prop} {O : R → Prop} {ε : R}
    (hε : ε * ε = ε) {B C M : Matrix (Fin n) (Fin n) R} {u : Fin n → R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B *ᵥ z)
    (hCB : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R))
    (hM : ε • M = ε • (B * Matrix.diagonal u * C)) :
    GlobalTheory.DivDual.Dv Λ O ε u M := by
  have key : ∀ y z : Fin n → R, ε • y = ε • B *ᵥ z →
      ε • M *ᵥ y = ε • B *ᵥ (fun i => u i * z i) := by
    intro y z hyz
    have e1 : (fun i => u i * z i) = Matrix.diagonal u *ᵥ z := by
      funext i; simp [Matrix.mulVec_diagonal]
    have e2 : ε • (C *ᵥ (B *ᵥ z)) = ε • z := by
      rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, hCB, Matrix.smul_mulVec, Matrix.one_mulVec]
    calc ε • M *ᵥ y = (ε • M) *ᵥ y := (Matrix.smul_mulVec _ _ _).symm
      _ = (B * Matrix.diagonal u * C) *ᵥ (ε • y) := by
          rw [hM, Matrix.smul_mulVec, Matrix.mulVec_smul]
      _ = (B * Matrix.diagonal u) *ᵥ (ε • (C *ᵥ (B *ᵥ z))) := by
          rw [hyz, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            Matrix.mulVec_mulVec]
      _ = ε • B *ᵥ (fun i => u i * z i) := by
          rw [e2, e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  refine ⟨B, h1, h2, fun y hy => ?_, fun z hz => ⟨ε • B *ᵥ z, h1 z hz, key _ _ ?_⟩⟩
  · obtain ⟨z, hz, e⟩ := h2 y hy
    exact ⟨z, hz, key y z e⟩
  · rw [smul_smul, hε]

end GlobalTheory.SplitExist

namespace GlobalTheory.SplitExist



theorem split_exist : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ : 𝓞 D.host.E) (d : List ℤ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    d.length = V.rank → ∃ g : GA D V, SuppF V (e + cA D e) g ∧ DivAt V e (ϖ : D.host.E) d g := by
  intro D V P e ϖ d hI h1 h2 hd
  have he : e * e = e := hI.1.1
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis V he hI.2
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have hϖ : (ϖ : D.host.E) ≠ 0 := fun h0 => h2 (by
    have : ϖ = 0 := by exact_mod_cast h0
    rw [this]; exact zero_mem _)
  let u : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun i => finPart D (incA D ((ϖ : D.host.E) ^ (d.getD i.1 0)))
  let u' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun i => finPart D (incA D ((ϖ : D.host.E) ^ (-(d.getD i.1 0))))
  have huu : Matrix.diagonal u * Matrix.diagonal u' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    simp [u, u', ← map_mul, zpow_ne_zero _ hϖ]
  have key : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * (C * B) * Y) = finPart D e • (X * Y) := fun X Y => by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, c2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hmm : finPart D e • ((B * Matrix.diagonal u * C) * (B * Matrix.diagonal u' * C)) =
      finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
    have : (B * Matrix.diagonal u * C) * (B * Matrix.diagonal u' * C) =
        (B * Matrix.diagonal u) * (C * B) * (Matrix.diagonal u' * C) := by
      simp only [Matrix.mul_assoc]
    rw [this, key, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal u), huu, Matrix.one_mul, c1]
  obtain ⟨g, hg, hgm⟩ := GlobalTheory.SplitLift.split_lift V e hI.1 _ _ hmm
  exact ⟨g, fun i j => hg i j, (GlobalTheory.DivDual.divAt_iff V e _ d g).2 ⟨hd, dv_of_conj hee b1 b2 c2 hgm⟩⟩

end GlobalTheory.SplitExist
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj

namespace GlobalTheory.IdemAdj

theorem typeClosure_of_intertwine : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  intro E _ _ _ a π W _ _ ρ₀ U hU hst f hf u hu hcoef g
  haveI := hU
  let w : Kinf E a → U := fun k => ⟨cptOn π k u, hst k u hu⟩
  let A : (U →ₗ[ℂ] ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    { toFun := fun ℓ k => ℓ (w k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ev : GA E a → (U →ₗ[ℂ] ℂ) := fun h =>
    (LinearMap.proj h).comp ((Sm E a).subtype.comp (π.V.subtype.comp U.subtype))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    haveI hfr : Module.Free ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      Module.Free.of_divisionRing ℂ _
    haveI : Module.Projective ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      @Module.Projective.of_free _ _ _ _ _ hfr
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push_neg at hc
    exact hz (Subtype.ext (Subtype.ext (Subtype.ext (funext fun h => hc _ ⟨h, rfl⟩))))
  let L : U →ₗ[ℂ] ℂ :=
    (LinearMap.proj g).comp ((Sm E a).subtype.comp (π.V.subtype.comp (f.comp U.subtype)))
  have hL : L ∈ (AutFin.coeffSpan ρ₀).comap A := by
    have hmem : L ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    refine (Submodule.span_le.2 ?_) hmem
    rintro _ ⟨h, rfl⟩
    exact hcoef h
  have key : (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) = A L := by
    funext k
    show _ = (f (cptOn π k u)).1.1 g
    rw [hf k u hu, cptOn_val]
  rw [key]
  exact hL

end GlobalTheory.IdemAdj
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

theorem _root_.GlobalTheory.T.exponent_heckeChar_compNorm_conjEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (τ : E →+* ℂ), expo (compNorm E χ) (ComplexEmbedding.conjugate τ) = expo (compNorm E χ) τ := by
  first | exact @GlobalTheory.NormExpo.expo_compNorm_conjugate | exact GlobalTheory.NormExpo.expo_compNorm_conjugate | (intros; apply GlobalTheory.NormExpo.expo_compNorm_conjugate <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitHeckeCore

open Formalism.DivisionValues Formalism.IndefR Formalism.L2.Theta GlobalTheory.HeckeRational GlobalTheory.SplitHeckeAdj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_opMat_mem (R : RealDat D A Ks) (hf : R.IsFam) (t i a b) :
    (A.fam.R t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  obtain ⟨P, k⟩ := i
  show LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (A.heckeR t (P, k)) a b ∈ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(hf.degR t P).1]
    exact toMatrix_one_mem _ _ _ _
  rcases le_or_gt k D.sp.X'.rank with hk' | hk'
  · exact rows_dcOp_mem_cmMax R hf.tie t _ _ ((R.B.R t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
  · rw [(hf.degR t P).2 k hk', map_zero]
    exact Subfield.zero_mem _

theorem lifts_opMat_mem (R : RealDat D A Ks) (hf : R.IsFam) (j t i a b) :
    (A.fam.L j t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  obtain ⟨P, k⟩ := i
  show LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (A.heckeL j t (P, k)) a b ∈ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(hf.degL j t P).1]
    exact toMatrix_one_mem _ _ _ _
  rcases le_or_gt k (Vc D j).rank with hk' | hk'
  · exact lifts_dcOp_mem_cmMax R hf.tie j t _ _ ((R.B.L j t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
  · rw [(hf.degL j t P).2 k hk', map_zero]
    exact Subfield.zero_mem _

theorem hecke_okH_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (_F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t, (A.fam.R t).OkH ∧ Formalism.L2.Col.PairComm (A.fam.R t).op) ∧ ∀ j t, (A.fam.L j t).OkH ∧ Formalism.L2.Col.PairComm (A.fam.L j t).op := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ hl hf hm
  obtain ⟨gramR, c0R, c0L, tie⟩ := hf.tie
  have honto : ∀ t PP, Bridge.SplitOff PP ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))) → ∃ P, R.pl P = PP :=
    fun t PP hP => hf.pl_onto PP (splitOff_mono Set.subset_union_left hP)
  have hS : ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
    fun t PP hP => hP.elim (fun h1 => Or.inl (hf.Sb h1)) Or.inr
  refine ⟨fun t => ?_, fun j t => ?_⟩
  · obtain ⟨c, hc⟩ := hl.βX
    rw [one_pow] at hc
    have h := side_adj_comm D.sp.X' R.βX R.ΛX (R.datXt t) hc R.pl (A.ok t) _ (tie.ok t) (honto t) (hS t)
      R.cX.coef.ρ (fun γ => hm.cX.2.1 γ) D.what₂.embLL (A.MtildeCSD t) (R.B.R t).pres (A.heckeR t)
      (R.B.R t).hecke (hf.degR t)
    exact ⟨⟨rows_opMat_mem R hf t, h.1⟩, h.2⟩
  · obtain ⟨c, hc⟩ := hl.βV j
    rw [one_pow] at hc
    have h := side_adj_comm (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) hc R.pl (A.ok t) _ (tie.ok t) (honto t) (hS t)
      (R.cV j).coef.ρ (fun γ => (hm.cV j).2.1 γ) D.what₂.embLL (A.MtCSD j t) (R.B.L j t).pres (A.heckeL j t)
      (R.B.L j t).hecke (hf.degL j t)
    exact ⟨⟨lifts_opMat_mem R hf j t, h.1⟩, h.2⟩

end GlobalTheory.SplitHeckeCore

end
end
