module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle031
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.VecVMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.HelpSng
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVKer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle022
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVGeo

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField

namespace Formalism.L2.SG.Pf.AllRowsFin

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.AllRowsOf Formalism.MainNotions.ArithmeticCylinders
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsConv

variable {D : D7} (X : HidaSetting D)

def V : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal

theorem g_pos : 1 ≤ X.B.g := Nat.one_le_iff_ne_zero.2 (Formalism.L2.SG.Pf.RowDictPf.level_ne_zero X)

theorem Kg_fin : X.B.μf (X.B.I.Kg X.B.g) < ⊤ := by
  have hK : IsCompact X.B.I.Kset := Formalism.L2.SG.Closed.AutKCompact_holds X.B.I
  exact lt_of_le_of_lt (measure_mono fun x hx => hx.1) hK.measure_lt_top

theorem V_pos : 0 < V X := by
  have hpos : 0 < X.B.μf (X.B.I.Kg X.B.g) :=
    (X.B.I.topf_open X.B.g (g_pos X)).measure_pos X.B.μf ⟨1, Formalism.L2.SG.AllRowsOf.one_mem_Kg X⟩
  exact ENNReal.toReal_pos hpos.ne' (Kg_fin X).ne

theorem V_ne : (V X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (V_pos X).ne'

def BiInv (f : X.B.I.Gf → ℂ) : Prop :=
  (∀ x, f x ≠ 0 → x ∈ X.B.I.Kset) ∧ (∀ x, ∀ n ∈ X.B.I.Kg X.B.g, f (x * n) = f x) ∧
    (∀ x, ∀ n ∈ X.B.I.Kg X.B.g, f (n * x) = f x)

theorem biInv_e : BiInv X X.B.e := by
  refine ⟨X.B.e_adm.2.2.2.2.1, fun x n hn => ?_, fun x n hn => ?_⟩
  · have := X.B.e_adm.2.2.2.2.2.1 x 1 (Formalism.L2.SG.AllRowsOf.one_mem_Kg X) n hn
    rwa [one_mul] at this
  · have := X.B.e_adm.2.2.2.2.2.1 x n hn 1 (Formalism.L2.SG.AllRowsOf.one_mem_Kg X)
    rwa [mul_one] at this

theorem biInv_egA (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ γ P : G0g D.nd, a.coeff (P⁻¹ * γ * P) = a.coeff γ) :
    BiInv X (egA X a) := by
  refine ⟨fun x hx => by_contra fun h => hx (egA_of_not_mem X a h), fun x n hn => egA_mul X a x hn, fun x n hn => ?_⟩
  by_cases hx : x ∈ X.B.I.Kset
  · have hnx : n * x ∈ X.B.I.Kset := K_mul X.B.I hn.1 hx
    have hn1 : rhoX X ⟨n, hn.1⟩ = 1 := (rhoX_eq_one_iff X _).2 hn
    have e : rhoX X ⟨n * x, hnx⟩ = rhoX X ⟨x, hx⟩ := by
      rw [show (⟨n * x, hnx⟩ : KSub X.B.I) = ⟨n, hn.1⟩ * ⟨x, hx⟩ from rfl, map_mul, hn1, one_mul]
    calc egA X a (n * x) = a.coeff (rhoX X ⟨n * x, hnx⟩) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) :=
          egA_rhoX X a ha ⟨n * x, hnx⟩
      _ = a.coeff (rhoX X ⟨x, hx⟩) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) := by rw [e]
      _ = egA X a x := (egA_rhoX X a ha ⟨x, hx⟩).symm
  · have hnx : n * x ∉ X.B.I.Kset := fun h => hx (by
      have := K_mul X.B.I (K_inv X.B.I hn.1) h
      rwa [inv_mul_cancel_left] at this)
    rw [egA_of_not_mem X a hnx, egA_of_not_mem X a hx]

theorem biInv_eT (S : Set (Tup2 D)) : BiInv X (eT X S) :=
  ⟨fun x hx => by_contra fun h => hx (eT_of_not_mem X S h), fun x n hn => eT_mul X S x hn,
    fun x n hn => eT_mul_left X S x hn⟩

theorem conv_sum [Fintype (KSub X.B.I ⧸ KgN X.B.I X.B.g)] {f₁ f₂ : X.B.I.Gf → ℂ} (hf₁ : BiInv X f₁) (hf₂ : BiInv X f₂) (x : X.B.I.Gf) :
    X.B.I.convF X.B.μf f₁ f₂ x = (V X : ℂ) * ∑ q : KSub X.B.I ⧸ KgN X.B.I X.B.g,
      f₁ ((q.out : KSub X.B.I) : X.B.I.Gf) * f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * x) := by
  rw [convF_fin X.B.I X.B.μf (g_pos X) (Kg_fin X) hf₁.1 hf₁.2.1 hf₂.2.2 x]
  rfl

instance instNeZeroG (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

instance finiteReductionGroup (D : D7) : Fintype (G0g D.nd) := by classical infer_instance

variable {X} (hS : Function.Surjective (rhoX X))
include hS

def sec (γ : G0g D.nd) : KSub X.B.I := Classical.choose (hS γ)

theorem rho_sec (γ : G0g D.nd) : rhoX X (sec hS γ) = γ := Classical.choose_spec (hS γ)

def hat (f : X.B.I.Gf → ℂ) (γ : G0g D.nd) : ℂ := (V X : ℂ) * f (sec hS γ)

theorem val_hat {f : X.B.I.Gf → ℂ} (hf : BiInv X f) (x : KSub X.B.I) :
    f x = hat hS f (rhoX X x) / (V X : ℂ) := by
  unfold hat
  have hk' : (((sec hS (rhoX X x))⁻¹ * x : KSub X.B.I) : X.B.I.Gf) ∈ X.B.I.Kg X.B.g :=
    (rhoX_eq_one_iff X _).1 (by rw [map_mul, map_inv, rho_sec, inv_mul_cancel])
  have e : (x : X.B.I.Gf) =
      (sec hS (rhoX X x) : X.B.I.Gf) * (((sec hS (rhoX X x))⁻¹ * x : KSub X.B.I) : X.B.I.Gf) := by
    push_cast
    group
  rw [e, hf.2.1 _ _ hk', mul_div_cancel_left₀ _ (V_ne X)]

theorem ker_eq : (rhoX X).ker = KgN X.B.I X.B.g := by
  ext x
  rw [MonoidHom.mem_ker, rhoX_eq_one_iff]
  rfl

def qEquiv : (KSub X.B.I ⧸ KgN X.B.I X.B.g) ≃* G0g D.nd :=
  (QuotientGroup.quotientMulEquivOfEq (ker_eq hS).symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ hS)

theorem qEquiv_mk (k : KSub X.B.I) : qEquiv hS (QuotientGroup.mk k) = rhoX X k := rfl

theorem qEquiv_out (q : KSub X.B.I ⧸ KgN X.B.I X.B.g) : qEquiv hS q = rhoX X q.out := by
  have h := qEquiv_mk hS q.out
  rwa [QuotientGroup.out_eq'] at h

def instFintypeQ : Fintype (KSub X.B.I ⧸ KgN X.B.I X.B.g) := Fintype.ofEquiv _ (qEquiv hS).symm.toEquiv

theorem biInv_conv {f₁ f₂ : X.B.I.Gf → ℂ} (hf₁ : BiInv X f₁) (hf₂ : BiInv X f₂) :
    BiInv X (X.B.I.convF X.B.μf f₁ f₂) := by
  haveI := instFintypeQ hS
  refine ⟨fun x hx => ?_, fun x n hn => ?_, fun x n hn => ?_⟩
  · by_contra hxK
    apply hx
    rw [conv_sum X hf₁ hf₂]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q _ => ?_)
    have : f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * x) = 0 := by
      by_contra h
      apply hxK
      have := K_mul X.B.I (q.out : KSub X.B.I).2 (hf₂.1 _ h)
      rwa [mul_inv_cancel_left] at this
    rw [this, mul_zero]
  · rw [conv_sum X hf₁ hf₂, conv_sum X hf₁ hf₂]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mul_assoc, hf₂.2.1 _ n hn]
  · rw [conv_sum X hf₁ hf₂, conv_sum X hf₁ hf₂]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    set c : X.B.I.Gf := ((q.out : KSub X.B.I) : X.B.I.Gf)
    have hc : c⁻¹ ∈ X.B.I.Kset := K_inv X.B.I (q.out : KSub X.B.I).2
    have hn' : c⁻¹ * n * c⁻¹⁻¹ ∈ X.B.I.Kg X.B.g := Kg_conj' X.B.I X.B.g hc hn
    have e : c⁻¹ * (n * x) = (c⁻¹ * n * c⁻¹⁻¹) * (c⁻¹ * x) := by group
    rw [e, hf₂.2.2 _ _ hn']

theorem conv_hat {f₁ f₂ : X.B.I.Gf → ℂ} (hf₁ : BiInv X f₁) (hf₂ : BiInv X f₂) (γ : G0g D.nd) :
    hat hS (X.B.I.convF X.B.μf f₁ f₂) γ = ∑ δ : G0g D.nd, hat hS f₁ δ * hat hS f₂ (δ⁻¹ * γ) := by
  haveI := instFintypeQ hS
  have key : ∀ q : KSub X.B.I ⧸ KgN X.B.I X.B.g,
      hat hS f₁ (qEquiv hS q) * hat hS f₂ ((qEquiv hS q)⁻¹ * γ) =
        (V X : ℂ) * ((V X : ℂ) * (f₁ ((q.out : KSub X.B.I) : X.B.I.Gf) *
          f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * (sec hS γ : X.B.I.Gf)))) := by
    intro q
    have hm : ((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * (sec hS γ : X.B.I.Gf) ∈ X.B.I.Kset :=
      K_mul X.B.I (K_inv X.B.I (q.out : KSub X.B.I).2) (sec hS γ).2
    have e2 : rhoX X ⟨_, hm⟩ = (qEquiv hS q)⁻¹ * γ := by
      have : (⟨_, hm⟩ : KSub X.B.I) = (q.out)⁻¹ * sec hS γ := rfl
      rw [this, map_mul, map_inv, rho_sec, qEquiv_out]
    have h1 : hat hS f₁ (rhoX X q.out) = (V X : ℂ) * f₁ ((q.out : KSub X.B.I) : X.B.I.Gf) := by
      rw [val_hat hS hf₁ q.out]; field_simp [V_ne X]
    have h2 : hat hS f₂ (rhoX X ⟨_, hm⟩) = (V X : ℂ) * f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * (sec hS γ : X.B.I.Gf)) := by
      rw [val_hat hS hf₂ ⟨_, hm⟩]; field_simp [V_ne X]
    rw [qEquiv_out, ← qEquiv_out hS q, ← e2, qEquiv_out, h1, h2]
    ring
  calc hat hS (X.B.I.convF X.B.μf f₁ f₂) γ = (V X : ℂ) * X.B.I.convF X.B.μf f₁ f₂ (sec hS γ) := rfl
    _ = (V X : ℂ) * ((V X : ℂ) * ∑ q : KSub X.B.I ⧸ KgN X.B.I X.B.g, f₁ ((q.out : KSub X.B.I) : X.B.I.Gf) *
          f₂ (((q.out : KSub X.B.I) : X.B.I.Gf)⁻¹ * (sec hS γ : X.B.I.Gf))) := by rw [conv_sum X hf₁ hf₂]
    _ = ∑ q : KSub X.B.I ⧸ KgN X.B.I X.B.g, hat hS f₁ (qEquiv hS q) * hat hS f₂ ((qEquiv hS q)⁻¹ * γ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => (key q).symm
    _ = ∑ δ : G0g D.nd, hat hS f₁ δ * hat hS f₂ (δ⁻¹ * γ) :=
      Fintype.sum_equiv (qEquiv hS).toEquiv _ _ (fun _ => rfl)

theorem hat_inj {f f' : X.B.I.Gf → ℂ} (hf : BiInv X f) (hf' : BiInv X f') (h : ∀ γ, hat hS f γ = hat hS f' γ) :
    f = f' := by
  funext x
  by_cases hx : x ∈ X.B.I.Kset
  · have e1 := val_hat hS hf ⟨x, hx⟩
    have e2 := val_hat hS hf' ⟨x, hx⟩
    simp only at e1 e2
    rw [e1, e2, h]
  · have h1 : f x = 0 := by
      by_contra h0
      exact hx (hf.1 x h0)
    have h2 : f' x = 0 := by
      by_contra h0
      exact hx (hf'.1 x h0)
    rw [h1, h2]

theorem hat_egA (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ γ P : G0g D.nd, a.coeff (P⁻¹ * γ * P) = a.coeff γ)
    (γ : G0g D.nd) : hat hS (egA X a) γ = a.coeff γ := by
  unfold hat
  rw [egA_rhoX (X := X) a ha, rho_sec]
  show (V X : ℂ) * (a.coeff γ / (V X : ℂ)) = a.coeff γ
  field_simp [V_ne X]

theorem hat_eT (S : Set (Tup2 D)) (γ : G0g D.nd) :
    hat hS (eT X S) γ = ∑ δ : G0g D.nd, hat hS X.B.e δ * (ES S).coeff (δ⁻¹ * γ) := by
  unfold eT
  rw [conv_hat hS (biInv_e X) (biInv_egA X _ (ES_conj S))]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [hat_egA hS _ (ES_conj S)]

theorem hat_e_idem (γ : G0g D.nd) : ∑ δ : G0g D.nd, hat hS X.B.e δ * hat hS X.B.e (δ⁻¹ * γ) = hat hS X.B.e γ := by
  rw [← conv_hat hS (biInv_e X) (biInv_e X), X.B.e_adm.2.1]

end Formalism.L2.SG.Pf.AllRowsFin
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.RhoSurjW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.AllRowsOf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i
  simp [PI.FinKW.vecV, map_sub]

theorem vecV_nsmul (v : HeightOneSpectrum (𝓞 X.B.I.F)) (c : ℕ)
    (a : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (c • a) = c • PI.FinKW.vecV X.B.I v a := by
  funext i
  simp [PI.FinKW.vecV]

theorem exists_cofactor (p : TypX X) : ∃ c : ℕ, (X.B.g : ℕ) = gOf p * c := by
  rw [X.g_eq]
  unfold gOf
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨D.host.g 0, mul_comm _ _⟩

theorem piV_mem_KgX (x : X.B.I.Gf) (hx : x ∈ X.B.I.Kg X.B.g) (p : TypX X) :
    piV X.B.I p.1 (tf X.B.I hb x) ∈ MassDataIdxSteps.KgX X p := by
  have hKf := (Bridge_mem_Kf_iff X.B.I hb x).2 hx.1
  rw [Kf, Subgroup.mem_iInf] at hKf
  refine ⟨hKf p.1, ?_⟩
  intro y hy
  obtain ⟨c, hc⟩ := exists_cofactor X p
  obtain ⟨u, huv, huw⟩ := PI.FinKW.local_vector_lift X.B.I p.1 y
  have huL : u ∈ X.B.I.Lf := PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective X.B.I u fun w => by
    by_cases hw : w = p.1
    · subst hw
      rw [huv]
      exact hy
    · rw [huw w hw]
      exact zero_mem _
  obtain ⟨z, hzL, hz⟩ := hx.2 u huL
  have hfx : X.B.I.fmat x = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := (toHA_isBridge X.B.I hb (1, x)).2
  refine ⟨c • PI.FinKW.vecV X.B.I p.1 z, nsmul_mem (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I z hzL p.1) c, ?_⟩
  have e := congrArg (PI.FinKW.vecV X.B.I p.1) hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecV_sub, hfx, PI.FinKW.vecV_mulVec, huv, Nat.cast_smul_eq_nsmul,
    vecV_nsmul] at e
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_smul, ← hc]
  exact e

end Loc

section Count

variable {D : D7} (X : HidaSetting D)

theorem card_target :
    Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = Nat.card (G0g D.nd) := by
  classical
  have hT : (Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod]
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.prod_typ X (fun g => (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod g)) : ℝ))]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.ggC_eq D.R (gOf p)]
    rfl
  have hG : (Nat.card (G0g D.nd) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sigma, Fin.prod_univ_two]
    have e : ∀ k : Fin 2, ∏ _v : D.nd.PlG k, (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) =
        (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g k))) : ℝ) ^ D.R.f := fun k => by
      rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
      rfl
    exact congrArg₂ (· * ·) (e 0) (e 1)
  exact_mod_cast hT.trans hG.symm

end Count

theorem reduction_map_surjective : RhoSurj := by
  intro D X
  classical
  let hb : AdBridgeIso X.B.I := (Formalism.L2.SG.Closed.adelic_isomorphism_statement X.B.I).1
  have hK : ∀ p : TypX X, ((KvS X p : Subgroup _) : Set (MassDataIdxSteps.HAp X p)) = MassDataIdxSteps.KvX X p := by
    intro p
    obtain ⟨K, hKs, -, -, -⟩ := Formalism.L2.SG.Pf.MassDataX.stK_holds X p
    have e : KvS X p = K := by
      have e : (K : Set _) = Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1 := hKs
      rw [KvS, ← e, Subgroup.closure_eq]
    rw [e]
    exact hKs
  choose ρ hρ hker using fun p : TypX X => Formalism.L2.SG.Pf.MassDataX.stRed_holds X p (KvS X p) (hK p)
  let ψ : KsetSub X.B.I →* ∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MonoidHom.pi fun p => (ρ p).comp (Pi.evalMonoidHom (fun p => KvS X p) p)).comp (phiK X hb)
  have hψ : Function.Surjective ψ := by
    intro t
    choose a ha using fun p => hρ p (t p)
    obtain ⟨k, hk⟩ := phiK_surjective X hb single_component_surjective a
    refine ⟨k, funext fun p => ?_⟩
    show ρ p (phiK X hb k p) = t p
    rw [hk]
    exact ha p
  let ι : KSub X.B.I → KsetSub X.B.I := fun x => ⟨x.1, x.2⟩
  have hψι : ∀ x y : KSub X.B.I, rhoX X x = rhoX X y → ψ (ι x) = ψ (ι y) := by
    intro x y hxy
    have h1 : rhoX X (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hg := (rhoX_eq_one_iff X _).1 h1
    have h2 : ψ (ι (x⁻¹ * y)) = 1 := by
      funext p
      show ρ p (phiK X hb (ι (x⁻¹ * y)) p) = 1
      exact (hker p _).2 (RhoSurjW.piV_mem_KgX X hb _ hg p)
    have h3 : ι (x⁻¹ * y) = (ι x)⁻¹ * ι y := rfl
    rw [h3, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let f : (rhoX X).range → (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) :=
    fun r => ψ (ι (MonoidHom.mem_range.1 r.2).choose)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨k, hk⟩ := hψ t
    let x : KSub X.B.I := ⟨k.1, k.2⟩
    let r : (rhoX X).range := ⟨rhoX X x, x, rfl⟩
    exact ⟨r, (hψι _ x (MonoidHom.mem_range.1 r.2).choose_spec).trans hk⟩
  have hle : Nat.card (G0g D.nd) ≤ Nat.card (rhoX X).range := by
    rw [← RhoSurjW.card_target X]
    exact Nat.card_le_card_of_surjective f hf
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_le_card _ hle)

end Formalism.L2.SG.Pf.RhoSurjW
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

def piW : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
  ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [w.2.2]; exact b.2)) w.2.2⟩

def blkW : Fin (D.R.rS + 1) → ℕ := fun i => blkOf w.1 i.val

theorem piW_invol (a : Fin (D.R.rS + 1)) : piW w (piW w a) = a := by
  apply Fin.ext
  show ptPar w.1 (ptPar w.1 a.val) = a.val
  exact ptPar_invol w.1 a.val (by rw [w.2.2]; exact a.2)

theorem piW_blk (a : Fin (D.R.rS + 1)) : blkW w (piW w a) = blkW w a := by
  show blkOf w.1 (ptPar w.1 a.val) = blkOf w.1 a.val
  exact blkOf_ptPar w.1 a.val (by rw [w.2.2]; exact a.2)

theorem piW_anti (a b : Fin (D.R.rS + 1)) (h : blkW w a = blkW w b) (hab : a < b) : piW w b < piW w a := by
  show ptPar w.1 b.val < ptPar w.1 a.val
  exact ptPar_anti w.1 a.val b.val (by rw [w.2.2]; exact b.2) hab h

def Fw (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ := frm X u D.host.rdE v

def Gw (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ :=
  fun b => uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b

theorem hGG_w (v : InfinitePlace X.B.I.F) (a b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (Gw X u u' w v a) (Gw X u u' w v b) = lastDiag (-((Tw u' : ℝ) : ℂ)) a b := by
  show hJ (X.B.I.ε v) (uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v a)
    (uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b) = _
  rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj, Matrix.mulVec_mulVec]
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by
    simp [uMat]
  rw [h1, Matrix.one_mulVec]
  exact gram_frm X v u' D.host.rdE a b

theorem hZ_w (hw : OkPt X u u' w) (v : InfinitePlace X.B.I.F) (c b : Fin (D.R.rS + 1)) :
    Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) c b ≠ 0 ↔ c = piW w b := by
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dite_eq_left hw.1]
    exact hw.1.choose_spec
  have hk : ∀ a : Fin (D.R.rS + 1), (((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - a.1))⁻¹ ≠ 0 := fun a =>
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast rdE_pos_c.ne'))
  have hZ : Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) c b =
      (star ((((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - c.1))⁻¹) * (((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - b.1))⁻¹) *
        ZX X u u' 1 (gamW X u u' w) v c b := by
    simp only [Zm, Matrix.of_apply, Fw, Gw, ZX, Formalism.L2.SG.RealObj.Zhat, frm, famSc, hJ, Matrix.mulVec_smul, star_smul,
      Complex.ofReal_one, one_pow, inv_one, one_smul]
    simp [dotProduct_smul, smul_dotProduct]
    ring
  have h2 := congrFun (congrFun (hrep v) c) b
  simp only [Formalism.L2.SG.RealObj.ZhatO] at h2
  have h3 : ZX X u u' 1 (gamW X u u' w) v c b ≠ 0 ↔ Formalism.L2.SG.RealObj.ptC X v w c b ≠ 0 := by
    rw [← h2]
    simp
  have hb : b.val < (w.1.map Prod.snd).sum := by rw [w.2.2]; exact b.2
  rw [hZ, mul_ne_zero_iff, h3]
  simp only [Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, Formalism.MainNotions.S.ptMat]
  rw [ptEntry_eq w.1 c.val b.val hb]
  simp only [ne_eq, map_eq_zero_iff _ (X.B.I.φ v).injective, EmbeddingLike.map_eq_zero_iff, ite_eq_right_iff,
    not_forall, exists_prop]
  constructor
  · rintro ⟨_, h, _⟩
    exact Fin.ext h
  · intro h
    exact ⟨mul_ne_zero (star_ne_zero.mpr (hk c)) (hk b), congrArg Fin.val h, ptSc_ne w.1 w.2.1 b.val hb⟩

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
