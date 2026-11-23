module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionConjugacy
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObjInhab
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRho

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA

variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))

def RedMatB (p : ℕ) {m : ℕ} (b : Fin m → Fin I.n → I.E) (x : I.Gf) (M : Matrix (Fin m) (Fin m) (ZMod p)) : Prop :=
  ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w

theorem redMat0_of {p m : ℕ} {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf}
    {M : Matrix (Fin m) (Fin m) (ZMod p)} (h : RedMatB I w p b x M) : RedMat0 I w p x M := ⟨b, hb, h⟩

theorem natSmul_Lq (k : ℕ) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lq I w) :
    (k : I.E ⊗[I.F] Af I.F) • z ∈ Lq I w := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hz k

theorem redMatB_exists {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} (hx : x ∈ I.Kset) :
    ∃ M : Matrix (Fin m) (Fin m) (ZMod p), RedMatB I w p b x M := by
  have : NeZero p := ⟨hp.ne_zero⟩
  choose c hc using fun i => coords I w hp hcard hb (K_mv I hx (DictLat.iv_mem I (hb.1 i)))
  refine ⟨Matrix.of fun j i => ((c i j : ℤ) : ZMod p), fun i => ?_⟩
  have h2 : ∑ j, ((((c i j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    exact sum_mem fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)
  have := sub_mem (hc i) h2
  convert this using 1
  simp only [Matrix.of_apply]
  abel

theorem mkQ_natSmul (k : ℕ) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (Lq I w).mkQ ((k : I.E ⊗[I.F] Af I.F) • v) = ((k : ℤ)) • (Lq I w).mkQ v := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, natCast_zsmul]

theorem redMatB_unique {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ} (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} {M M' : Matrix (Fin m) (Fin m) (ZMod p)}
    (h : RedMatB I w p b x M) (h' : RedMatB I w p b x M') : M = M' := by
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  ext j i
  have hdiff : ∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
      ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) ∈ Lq I w := by
    have := sub_mem (h i) (h' i)
    convert this using 1
    abel
  have hz : ∑ l, ((((M' l i).val : ℕ) : ℤ) - (((M l i).val : ℕ) : ℤ)) • (Lq I w).mkQ (iv I (b l)) = 0 := by
    have h0 : (Lq I w).mkQ (∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
        ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hdiff

    rw [map_sub, map_sum, map_sum] at h0
    simp only [mkQ_natSmul] at h0
    rw [← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => sub_smul _ _ _
  have hj := Formalism.L2.SG.Pf.RedConj0Pf.zcoef_A I w p hp hcard hb _ hz j
  have hj' : ((M' j i).val : ZMod p) - ((M j i).val : ZMod p) = 0 := by exact_mod_cast hj
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_eq_zero] at hj'
  exact hj'.symm

theorem redMatB_mul {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : ∀ i, b i ∈ I.L) {x y : I.Gf} (hx : x ∈ I.Kset)
    {M N : Matrix (Fin m) (Fin m) (ZMod p)} (hM : RedMatB I w p b x M) (hN : RedMatB I w p b y N) :
    RedMatB I w p b (x * y) (M * N) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro i
  have hAB : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
  have s1 : I.fmat x *ᵥ (I.fmat y *ᵥ iv I (b i)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) ∈ Lq I w := by
    have := stab_w I w hx (hN i)
    rw [Matrix.mulVec_sub, Matrix.mulVec_sum] at this
    simpa only [Matrix.mulVec_smul] using this
  have s2 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun k _ => ?_
    rw [← smul_sub]
    exact natSmul_Lq I w _ (hM k)
  have e3 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_natCast, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_mul, mul_comm]
  have s3 : ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, ((((M * N) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    have hc : (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : ZMod p) = (M * N) j i := by
      rw [Int.cast_natCast, Nat.cast_sum, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have := val_sub I w hp hcard (hb j) ((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ)
    rw [hc] at this
    have := neg_mem this
    rwa [neg_sub] at this
  rw [e3] at s2
  have := add_mem (add_mem s1 s2) s3
  rw [hAB, ← Matrix.mulVec_mulVec]
  convert this using 1
  abel

theorem redMatB_one {p : ℕ} (hp : p.Prime) {m : ℕ} (b : Fin m → Fin I.n → I.E) :
    RedMatB I w p b 1 (1 : Matrix (Fin m) (Fin m) (ZMod p)) := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  intro i
  have e : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      iv I (b i) := by
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
    · intro j _ hj; simp [Matrix.one_apply_ne hj]
    · simp
  rw [e, fmat_one, Matrix.one_mulVec, sub_self]
  exact zero_mem _

structure RedB (I : AutInst) (m : ℕ) where
  w : HeightOneSpectrum (𝓞 I.E)
  p : ℕ
  hp : p.Prime
  hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p
  hm : m = I.n
  b : Fin m → Fin I.n → I.E
  hb : IsRedBasis0 I w b

variable {I} {m : ℕ}


open Classical in
def matB (R : RedB I m) (x : I.Gf) : Matrix (Fin m) (Fin m) (ZMod R.p) :=
  if hx : x ∈ I.Kset then Classical.choose (redMatB_exists I R.w R.hp R.hcard R.hb hx) else 0

theorem matB_spec (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) : RedMatB I R.w R.p R.b x (matB R x) := by
  unfold matB; rw [dite_eq_left hx]; exact Classical.choose_spec (redMatB_exists I R.w R.hp R.hcard R.hb hx)

theorem matB_eq (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) {M : Matrix (Fin m) (Fin m) (ZMod R.p)}
    (h : RedMatB I R.w R.p R.b x M) : matB R x = M :=
  redMatB_unique I R.w R.hp R.hcard R.hm R.hb (matB_spec R hx) h

theorem matB_mul (R : RedB I m) {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) :
    matB R (x * y) = matB R x * matB R y :=
  matB_eq R (K_mul I hx hy) (redMatB_mul I R.w R.hp R.hcard R.hb.1 hx (matB_spec R hx) (matB_spec R hy))

theorem matB_one (R : RedB I m) : matB R 1 = 1 := matB_eq R (K_one I) (redMatB_one I R.w R.hp R.b)

def rhoB (R : RedB I m) : Formalism.L2.SG.AllRowsOf.KSub I →* GL (Fin m) (ZMod R.p) :=
  MonoidHom.toHomUnits
    { toFun := fun x => matB R x
      map_one' := matB_one R
      map_mul' := fun x y => matB_mul R x.2 y.2 }

theorem rhoB_val (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) = matB R x := rfl

theorem rhoB_spec (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    RedMatB I R.w R.p R.b x ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) :=
  matB_spec R x.2

end Formalism.L2.SG.Pf.AllRowsRho
end
end

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.EnergyCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem normSq_cTorBase (g : ℝ) :
    star (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) * (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) =
      (((g / (2 * Real.pi)) ^ 2 : ℝ) : ℂ) := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  set a : ℝ := g / (2 * Real.pi) with ha
  have hk : -(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ)) = -Complex.I * (a : ℂ) := by
    rw [ha]; push_cast; field_simp
  rw [hk, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow]
  linear_combination (-(a : ℂ) ^ 2) * Complex.I_sq

theorem zhatTr_carrierOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀))) :
    (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).FromX →
    0 < (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).S.g →
    ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
      RealObj.Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (Formalism.MainNotions.S.uMat g) = Matrix.diagonal cv →
      trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g ∈
          Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS ∧
        Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (T ((tauE X e).symm v)).base.z (T ((tauE X e).symm v)).base.z'
          (trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g) =
          Matrix.diagonal (Fin.snoc (α := fun _ => ℂ)
            (Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
              (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv).1
            (Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
              (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv).2) ∧
        Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
                  (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv ∈
          Formalism.FourierDecayAlt.JF.QDom D.R.k D.R.rS (T ((tauE X e).symm v)).base.z (T ((tauE X e).symm v)).base.z' := by
  intro hFX hg v g cv hcv hZ
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hgg
  set κ : ℂ := -(Complex.I * ((gg : ℝ) : ℂ)) / (2 * (Real.pi : ℂ)) with hκ
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v))
      (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v))
      (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  refine ⟨Bridge.delta_GV hTr (uMat_unitary g), ?_, ?_⟩
  · have hz2 : (T ((tauE X e).symm v)).base.z = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u) := hz
    have hz2' : (T ((tauE X e).symm v)).base.z' = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u') := hz'
    rw [hz2, hz2']
    have h1 := Bridge.zhat_cs hTr hTr' (sc := 1) one_ne_zero (Formalism.MainNotions.S.uMat g)
    have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u))
        (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u'))
        (trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g) =
        Matrix.diagonal (fun a => star (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1 a)) *
          RealObj.Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (Formalism.MainNotions.S.uMat g) *
          Matrix.diagonal (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1) := h1
    rw [h1', hZ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    show _ = Matrix.diagonal (Fin.snoc (α := fun _ : Fin (D.R.rS + 1) => ℂ)
      (fun a : Fin D.R.rS => ((((gg : ℝ) / (2 * Real.pi)) ^ (2 * (D.R.rS - a.val)) : ℝ) : ℂ) * cv ⟨a.val, by omega⟩)
      (cv ⟨D.R.rS, by omega⟩))
    congr 1
    funext a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Fin.snoc_last, Bridge.lam_last, star_one, one_mul, mul_one]
      rfl
    · rw [Fin.snoc_castSucc]
      have hl : Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1 (Fin.castSucc i) = κ ^ (D.R.rS - i.val) := by
        unfold Bridge.lam
        rw [dite_eq_left (show ((Fin.castSucc i : Fin (D.R.rS + 1)) : ℕ) < D.R.rS from i.2)]
        simp [cTor, hκ]
      rw [hl, star_pow]
      have hcv' : cv (Fin.castSucc i) = cv ⟨i.val, by omega⟩ := rfl
      rw [hcv', show (star κ) ^ (D.R.rS - i.val) * cv ⟨i.val, by omega⟩ * κ ^ (D.R.rS - i.val) =
        (star κ * κ) ^ (D.R.rS - i.val) * cv ⟨i.val, by omega⟩ by ring, hκ, normSq_cTorBase, ← Complex.ofReal_pow,
        ← pow_mul]
  · have hg0 : (0 : ℝ) < gg := by exact_mod_cast hg
    refine ⟨fun a => ?_, ?_⟩
    · show ((((gg : ℝ) / (2 * Real.pi)) ^ (2 * (D.R.rS - a.val)) : ℝ) : ℂ) * cv ⟨a.val, by omega⟩ ≠ 0
      refine mul_ne_zero ?_ (hcv.1 _)
      have : (0 : ℝ) < (gg : ℝ) / (2 * Real.pi) := div_pos hg0 (by positivity)
      exact_mod_cast (pow_pos this _).ne'
    · rw [(hT _).1, (hT _).2]
      show ((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ) < Complex.normSq (cv ⟨D.R.rS, by omega⟩)
      have hG := hcv.2
      unfold Gv at hG
      rw [Dl_diagonal cv _ le_rfl, Dl_diagonal cv _ (Nat.le_succ _),
        Formalism.L2.SG.Pf.CarrierTop.prod_castLE_succ cv, norm_mul] at hG
      have hP : 0 < ‖∏ i : Fin D.R.rS, cv (Fin.castLE (Nat.le_succ D.R.rS) i)‖ :=
        norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hcv.1 _)
      have hlast : cv (Fin.last D.R.rS) = cv ⟨D.R.rS, by omega⟩ := rfl
      rw [hlast] at hG
      rw [Complex.normSq_eq_norm_sq]
      unfold Tw at hG
      nlinarith [sq_nonneg ‖∏ i : Fin D.R.rS, cv (Fin.castLE (Nat.le_succ D.R.rS) i)‖]

end Formalism.L2.SG.Pf.Carrier
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.JointPin

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf
  Formalism.L2.SG.Pf.Carrier.JointQuot Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.Pf.Carrier.EnergyPlace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def PinHyp (P : Parts X u u') (v : InfinitePlace X.B.I.F) (γ : Formalism.REAL.UJ (X.B.I.ε v))
    (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C6.IsRelevant (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ) ∧
  IsHaarLoc (StSet (NV X u v) (NV X u' v) γ) μRv ∧ IsQuotLoc μRv ν

def trMeas (P : Parts X u u') (v : InfinitePlace X.B.I.F) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Measure (Formalism.QuantumDeterminants.Mt P.S.G.k P.S.G.r) :=
  μRv.map (fun s => Matrix.of.symm (trG (P.Q v) (P.Qi v) s))

def PinCov (P : Parts X u u') : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (γ : Formalism.REAL.UJ (X.B.I.ε v)) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))),
    PinHyp P v γ μRv ν →
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) γ) =
      ((P.eP v).toContinuousLinearEquiv : _ →L[ℂ] X.Vloc u v).comp
        ((Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ) (trMeas P v μRv)
            (P.f (P.τ.symm v))).comp
          ((P.eQ v).symm.toContinuousLinearEquiv : X.Vloc u' v →L[ℂ] _))

def JointBridge (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  0 < sc → StRel X u u' → P.FromX → P.Base i0 i0' → (∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) →
  P.Built → ∀ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
  (∀ w, OkPt X u u' w → LocPin X u u' w νl) →
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' → ∀ v : InfinitePlace X.B.I.F,
    ∃ (γ' : Formalism.REAL.UJ (X.B.I.ε v)) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))), PinHyp P v γ' μRv ν ∧
      (∀ y : X.Vloc u' v,
        X.piLoc u v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h⁻¹)
          ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
            Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))
            (X.piLoc u' v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h') y)) =
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) γ') y) ∧
      Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ') (trMeas P v μRv) (P.f (P.τ.symm v)) =
        (((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))

def NormBridge (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.FromX → P.Built → 0 < P.S.g →
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    ∃ μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v)), PinHyp P v g μRv ν ∧
      JvX X u u' v g = (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) g) ∧
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) g) (trMeas P v μRv)
                (P.f (P.τ.symm v)))‖ =
        ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
          (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖

private theorem sum_norm_sq_apply_basis_indep {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (b : OrthonormalBasis ι ℂ Wq) (b' : OrthonormalBasis ι' ℂ Wq) (A : Wq →L[ℂ] Wp) :
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ‖A (b' i)‖ ^ 2 := by
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  have key : ∀ {κ : Type} [Fintype κ] (c : OrthonormalBasis κ ℂ Wq), ∑ i, ‖A (c i)‖ ^ 2 =
      (LinearMap.trace ℂ Wq (((ContinuousLinearMap.adjoint A).comp A : Wq →L[ℂ] Wq) : Wq →ₗ[ℂ] Wq)).re := by
    intro κ _ c
    rw [LinearMap.trace_eq_sum_inner _ c, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [key b, key b']

theorem hilbertSchmidt_conj_isometry {Wp Wq : Type} {V V' : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (e : Wp ≃ₗᵢ[ℂ] V) (e' : Wq ≃ₗᵢ[ℂ] V') (A : Wq →L[ℂ] Wp) :
    hs2 ((e.toContinuousLinearEquiv : Wp →L[ℂ] V).comp
      (A.comp (e'.symm.toContinuousLinearEquiv : V' →L[ℂ] Wq))) = ‖Formalism.FourierDecayAlt.B.hsVec A‖ ^ 2 := by
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  simp only [hs2, Formalism.FourierDecayAlt.B.hsVec, PiLp.norm_sq_eq_of_L2, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
  try simp only [PiLp.toLp_apply]
  have hb : ∀ i, e'.symm (stdOrthonormalBasis ℂ V' i) = ((stdOrthonormalBasis ℂ V').map e'.symm) i := fun i => by
    rw [OrthonormalBasis.map_apply]
  simp only [hb]
  exact sum_norm_sq_apply_basis_indep _ _ A

theorem placeJ_of_pin (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hpin : PinCov P) (hB : JointBridge P sc i0 i0') (hsc : 0 < sc) (hR : StRel X u u') (hFX : P.FromX)
    (hBase : P.Base i0 i0') (hEmb : ∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) (hBuilt : P.Built)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hνl : ∀ w, OkPt X u u' w → LocPin X u u' w νl) : PlaceJ P sc i0 i0' νl := by
  intro p w hp hrep hG h h' hD v y
  obtain ⟨γ', μRv, ν, hH, hJ, hO⟩ := hB hsc hR hFX hBase hEmb hBuilt νl hνl p w hp hrep hG h h' hD v
  rw [hJ y, hpin v γ' μRv ν hH, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hO]
  rfl

theorem placeNormG_of_pin (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hpin : PinCov P) (hB : NormBridge P hr)
    (hFX : P.FromX) (hBuilt : P.Built) (hg : 0 < P.S.g) : PlaceNormG P hr := by
  intro v g cv hc hZ
  obtain ⟨μRv, ν, hH, hJ, hn⟩ := hB hFX hBuilt hg v g cv hc hZ
  rw [hJ, hpin v g μRv ν hH, hilbertSchmidt_conj_isometry, hn]

theorem jointTensor_of_pin (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u') (hLU : LocUni X u u')
    (hGP : GlobProd X u u') (hpin : PinCov P) (hB : JointBridge P sc i0 i0') (hsc : 0 < sc) (hFX : P.FromX)
    (hBase : P.Base i0 i0') (hEmb : ∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) (hBuilt : P.Built) :
    P.JointTensor sc i0 i0' νq :=
  Formalism.L2.SG.Pf.Carrier.JointFinal.joint_tensor_factorization P sc i0 i0' νq hN hR hLU hGP
    (fun νl hνl => placeJ_of_pin P sc i0 i0' hpin hB hsc hR hFX hBase hEmb hBuilt νl hνl)

end Formalism.L2.SG.Pf.Carrier.JointPin
end
end
