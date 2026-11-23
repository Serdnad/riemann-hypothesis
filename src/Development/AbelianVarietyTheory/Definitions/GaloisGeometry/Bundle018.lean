module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Formalism.LocalToGlobal.Columns.RecLevelTop
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
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

structure InertJunk {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A3 : FamIn3 K G Pl0 I0 (List ℕ) T m) : Prop where
  R : ∀ t Q s, A3.heckeRI t (Q, s) = 0 ∨
    ∃ s', Formalism.L2.Col.InertTypeOk (A3.A.r + m * A3.A.t) s' ∧ A3.heckeRI t (Q, s) = A3.heckeRI t (Q, s')
  L : ∀ j t Q s, A3.heckeLI j t (Q, s) = 0 ∨
    ∃ s', Formalism.L2.Col.InertTypeOk (A3.A.r + A3.A.t) s' ∧ A3.heckeLI j t (Q, s) = A3.heckeLI j t (Q, s')

def GoodGeneric {K : Type} [Field K] (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0

def TrISepWith (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) →
      ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure RowDict (R : RealDat3 D A3 Ks) (t : T) (pl : (A3.rowI t).OpIx → Pl D.host.E)
    (cX c0 : (A3.rowI t).OpIx → List ℤ →₀ ℂ) : Prop where
  good : ∀ i, Good R.toRealDat t (pl i)
  op : ∀ h, IsOpsX R.toRealDat t h → ∀ i x, R.jX t ((A3.rowI t).opAll i x) = h (pl i) (cX i) (R.jX t x)
  mat : ∀ i, MatchE R.toRealDat t (pl i) (cX i) (c0 i)

structure LiftDict (R : RealDat3 D A3 Ks) (j : Fin D.R.m) (t : T) (pl : (A3.liftI j t).OpIx → Pl D.host.E)
    (cV cW : (A3.liftI j t).OpIx → List ℤ →₀ ℂ) : Prop where
  good : ∀ i, Good R.toRealDat t (pl i)
  op : ∀ h, IsOpsV R.toRealDat j t h → ∀ i x, R.jV j t ((A3.liftI j t).opAll i x) = h (pl i) (cV i) (R.jV j t x)
  mat : ∀ i, MatchW R.toRealDat j t (pl i) (cV i) (cW i)

def labW (j : Fin D.R.m) {I : Type} (pl : I → Pl D.host.E) (cW : I → List ℤ →₀ ℂ) (c : Pl D.host.E → List ℤ → ℂ) : I → ℂ :=
  fun i => evC (Wc D j) (pl i) (c (pl i)) (cW i)

end GlobalTheory.Hk3

end
end

section

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  (S : StepLevel F E σ J T f bad)

def basePts : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) where
  carrier := {k | k ∈ levelAfL σ J S.Lb ∧ ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1}
  one_mem' := ⟨one_mem _, fun _ _ => map_one _⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, fun v h => by rw [map_mul, ha.2 v h, hb.2 v h, mul_one]⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, fun v h => by rw [map_inv, ha.2 v h, inv_one]⟩

theorem mem_basePts_iff (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : k ∈ basePts S ↔
    k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL σ J v S.Lb) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1 := by
  rw [← and_assoc, ← GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin k]
  rfl

variable {S} (k : basePts S)

def basePtU : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨k.1, k.2.1.1⟩

theorem basePt_loc (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) k.1 ∈ levelVL σ J v S.Lb :=
  ((mem_basePts_iff S k.1).1 k.2).2.1 v

theorem conj_mem_iff {G : Type} [Group G] {H : Subgroup G} {a : G} (ha : a ∈ H) (x : G) : a * x * a⁻¹ ∈ H ↔ x ∈ H := by
  rw [H.mul_mem_cancel_right (inv_mem ha), H.mul_mem_cancel_left ha]

def moveLev : StepLevel F E σ J T f bad :=
  { S with
    Uloc := fun v => (S.Uloc v).comap (MulAut.conj (bc (prV (E := E) v) k.1)).toMonoidHom
    Uloc_le := fun v x hx => (conj_mem_iff (H := UPts σ J (v.adicCompletion F)) (basePt_loc k v).1 x).1 (S.Uloc_le v hx)
    Uloc_lev := fun v x hx => (conj_mem_iff (basePt_loc k v) x).1 (S.Uloc_lev v hx)
    Uloc_hyp := fun v hv hT => by
      ext x
      rw [S.Uloc_hyp v hv hT]
      exact conj_mem_iff (basePt_loc k v) x
    UlocAlt := fun v h => by
      rw [← S.UlocAlt v h, k.2.2 v h]
      ext x
      simp
    U := S.U.comap (MulAut.conj k.1).toMonoidHom
    U_eq := fun x => by
      show k.1 * x * k.1⁻¹ ∈ S.U ↔ _
      rw [S.U_eq, conj_mem_iff (H := UPts σ J (FiniteAdeleRing (𝓞 F) F)) (a := k.1) (basePtU k).2]
      refine and_congr_right fun _ => forall_congr' fun v => ?_
      rw [map_mul, map_mul, map_inv]
      rfl
    U_compact := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => k.1⁻¹ * x * k.1) :=
        (continuous_const.mul continuous_id).mul continuous_const
      convert S.U_compact.image hc using 1
      ext x
      constructor
      · intro hx
        exact ⟨k.1 * x * k.1⁻¹, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩
        show k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ ∈ S.U
        have e : k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ = y := by group
        rwa [e]
    U_open := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
        inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
      have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => basePtU k * x * (basePtU k)⁻¹) :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact S.U_open.preimage hc
    chi := S.chi.comp ((MulAut.conj k.1).toMonoidHom.subgroupComap S.U)
    chi_triv := fun x hx => S.chi_triv _ fun v hv => by
      show bc (prV (E := E) v) (k.1 * x.1 * k.1⁻¹) = 1
      rw [map_mul, map_mul, hx v hv, mul_one, ← map_mul, mul_inv_cancel, map_one] }

theorem mem_moveLev (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : x ∈ (moveLev k).U ↔ k.1 * x * k.1⁻¹ ∈ S.U := Iff.rfl

def toMoved (κ : S.U) : (moveLev k).U :=
  ⟨k.1⁻¹ * κ.1 * k.1, by
    have e : k.1 * (k.1⁻¹ * κ.1 * k.1) * k.1⁻¹ = κ.1 := by group
    rw [mem_moveLev, e]
    exact κ.2⟩

theorem cls_move_iff (x y : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    (Quotient.mk'' (x * basePtU k) : Cls (moveLev k)) = Quotient.mk'' (y * basePtU k) ↔
      (Quotient.mk'' x : Cls S) = Quotient.mk'' y := by
  refine (@DoubleCoset.eq _ _ _ _ _ _).trans (Iff.trans ?_ (@DoubleCoset.eq _ _ _ _ _ _).symm)
  refine exists_congr fun g => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨κ, hκ, e⟩
    refine ⟨basePtU k * κ * (basePtU k)⁻¹, hκ, ?_⟩
    rw [← mul_inv_cancel_right y (basePtU k), e]
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨(basePtU k)⁻¹ * κ * basePtU k, (toMoved k ⟨κ.1, hκ⟩).2, ?_⟩
    rw [e]
    group

theorem mem_hat_move_iff (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (y⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔
      ((y * k.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
        (moveLev k).Lb := by
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact (inv_mem k.2.1).2 _

theorem map_conj_move (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (moveLev k).U.map (MulAut.conj (y * k.1)).toMonoidHom = S.U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (mem_moveLev k κ).1 hκ, Eq.trans ?_ e⟩
    show y * (k.1 * κ * k.1⁻¹) * y⁻¹ = y * k.1 * κ * (y * k.1)⁻¹
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (toMoved k ⟨κ, hκ⟩).2, Eq.trans ?_ e⟩
    show y * k.1 * (k.1⁻¹ * κ * k.1) * (y * k.1)⁻¹ = y * κ * y⁻¹
    group

theorem bij_move {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : Function.Bijective fun c => (Quotient.mk'' (y c) : Cls S)) :
    Function.Bijective fun c => (Quotient.mk'' (y c * basePtU k) : Cls (moveLev k)) := by
  refine ⟨fun c c' e => h.1 ((cls_move_iff k _ _).1 e), fun q => ?_⟩
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨c, hc⟩ := h.2 (Quotient.mk'' (x * (basePtU k)⁻¹))
    refine ⟨c, ?_⟩
    have h := (cls_move_iff k _ _).2 hc
    rwa [inv_mul_cancel_right] at h

end Level

section Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}



def moveChart (K : LevelChart D T bad i hi stab lat) (k : basePts K.lev) : LevelChart D T bad i hi stab lat where
  lev := moveLev k
  y := fun c => K.y c * basePtU k
  y_bij := bij_move k K.y_bij
  y_lat := fun c x => (K.y_lat c x).trans (mem_hat_move_iff k (K.y c).1 x)
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := fun c γ => (K.stabI_range c γ).trans (SetLike.ext_iff.1 (map_conj_move k (K.y c).1) _).symm

end Chart

end GlobalTheory.TwU

end
end
