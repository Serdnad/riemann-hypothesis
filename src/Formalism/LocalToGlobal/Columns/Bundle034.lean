module

public import Formalism.LocalToGlobal.Columns.Bundle001
public import Formalism.LocalToGlobal.Columns.Record
public import Formalism.LocalToGlobal.Columns.ChainTwZero
public import Formalism.LocalToGlobal.Columns.Bundle015
import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
public import Formalism.LocalToGlobal.Columns.QthExistsBound
public import Formalism.LocalToGlobal.Columns.Bundle020
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ColBase where
  R : Ranks
  host : Host R
  sp : Spaces R host.F host.E
  what₂ : ColRows R
  eTau : what₂.Tau ≃ (R.Psi)
  [wordFin : Fintype what₂.Word]
  u₀ : what₂.Word
  hcW : what₂.Word → what₂.Tau → HCParam R
  [nfLL : NumberField what₂.LL]
  [starLL : StarRing what₂.LL]
  embE : host.E →+* what₂.LL

  cond : ℕ

  piG : Fin 2 → 𝓞 host.E

  T : what₂.Word → ℕ

  piT : what₂.Word → 𝓞 host.E

  tops : Finset what₂.Tau

attribute [instance] ColBase.wordFin ColBase.nfLL ColBase.starLL

namespace ColBase

variable (B : ColBase)

@[reducible] def X : Fields where
  F := B.host.F
  E := B.host.E
  K := B.what₂.LL
  starE := B.host.cmStar
  Tau := B.what₂.Tau
  deTau := Classical.decEq _
  emb := fun τ => B.embE.comp (B.host.sigmaOf (B.eTau τ : B.R.GG) : B.host.E →+* B.host.E)

@[reducible] def Pr : Primes B.X where
  cond := B.cond
  g := B.host.g
  piG := B.piG
  Word := B.what₂.Word
  deWord := Classical.decEq _
  T := B.T
  piT := B.piT

@[reducible] def W : Wts B.X B.what₂.Word B.R where
  row := fun τ => RowPar.of (B.hcW B.u₀ τ)
  hc := B.hcW
  tops := B.tops

@[reducible] def σ₀ : B.X.K →+* ℂ := B.what₂.embLL

end ColBase

structure ColDat extends ColBase where

  Ch : Chars toColBase.X toColBase.Pr R.m

  lev : ∀ j, LevFam toColBase.X.E toColBase.X.K (R.N j) toColBase.Pr.vGs := colLevS Ch

  lev0 : lev 0 = colLev Ch 0 := by
    exact colLevS_of_lt _ (Nat.lt_of_lt_of_le (by norm_num) (Ranks.two_le_m _))

  levP : LevFam toColBase.X.E toColBase.X.K (R.N R.m - 1) toColBase.Pr.vGs := (rowTyG Ch (rPsharp Ch)).inv

  Ps : CharT toColBase.X toColBase.Pr

  num : AtTNum

  plEq : what₂.places.Pl ≃ HeightOneSpectrum (𝓞 what₂.LL)
  hX : toColBase.X.Ok
  hPr : toColBase.Pr.Ok
  hPs : Ps.Ok

  star_cx : ∀ x : what₂.LL, what₂.embLL (star x) = starRingEnd ℂ (what₂.embLL x)

structure ColArgs (d : ColDat) where

  G : ChainGlob (Pr := d.Pr) d.W d.σ₀

  A : ∀ u : d.what₂.Word, ChainArg (Pr := d.Pr) d.W d.lev G u

  th : ∀ u : d.what₂.Word, ThArg (Pr := d.Pr) d.W d.lev u
  free : ∀ u : d.what₂.Word, (stepGSD (Pr := d.Pr) d.W d.lev u 0).Free
  rowOk : (rowGSD (Pr := d.Pr) d.W d.levP).Ok
  piT_off : ∀ (u : d.what₂.Word) (w : d.Pr.vGs), d.Pr.piT u ∉ w.1.asIdeal
  levExt : LevExt (Pr := d.Pr) d.lev (Finset.Subset.refl _) d.levP

namespace ColDat

variable (d : ColDat) (a : ColArgs d)

theorem f_eq : d.X.f = d.R.f := d.what₂.card_Tau

@[reducible] def chain (u : d.what₂.Word) : ColumnChain d.R d.what₂.Tau (d.hcW u) :=
  recChain (Pr := d.Pr) (W := d.W) (Λ := d.lev) d.hX d.σ₀ a.G u (a.A u)

@[reducible] def atT (u : d.what₂.Word) : ColumnsAtT d.R (d.chain a u) :=
  recAtT (Pr := d.Pr) (W := d.W) (Λ := d.lev) d.hX d.hPr d.f_eq d.σ₀ d.star_cx u a.G (a.A u) d.Ps d.hPs (a.free u) d.num

@[reducible] def per (u : d.what₂.Word) : PeriodMap d.R (d.chain a u) :=
  recPer (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hX d.σ₀ d.star_cx u a.G (a.A u) a.rowOk

@[reducible] def forms (u : d.what₂.Word) :
    MemberForms d.what₂.LL d.what₂.embLL d.what₂.places d.what₂.Tau (d.hcW u) (d.chain a u) (d.atT a u) (d.per a u) :=
  recFormsX (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hX d.hPr d.f_eq d.σ₀ d.star_cx u a.G (a.A u) d.Ps d.hPs
    (a.free u) d.num d.what₂.places d.plEq a.rowOk (a.piT_off u) a.levExt (a.th u)

def crd (i : ℕ) (hi : i ≤ d.R.m) : (d.sp.X i).V ≃ₗ[d.host.E] (Fin (d.R.N i) → d.host.E) :=
  (d.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft d.host.E d.host.E (finCongr (d.sp.X_rank i hi)).symm)

def repr (u : d.what₂.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : DecoSet (E := d.X.E) (n := d.R.N i) (ST := d.Pr.vT u) (SG := d.Pr.vGs) :=
  (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c


open Classical in
def clsLat (u : d.what₂.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : Submodule (𝓞 d.host.E) (d.sp.X i).V :=
  if hi : i ≤ d.R.m then
    (d.repr u i c).1.L.map (((d.crd i hi).symm : (Fin (d.R.N i) → d.host.E) →ₗ[d.host.E] (d.sp.X i).V).restrictScalars (𝓞 d.host.E))
  else (d.sp.X i).L0

@[reducible] def colRec : ColRec where
  R := d.R
  host := d.host
  sp := d.sp
  what₂ := d.what₂
  eTau := d.eTau
  u₀ := d.u₀
  hcW := d.hcW
  mem := fun u => ⟨d.chain a u, d.atT a u, d.per a u⟩
  embE := d.embE
  cOf := fun u => (d.piT d.u₀ : d.host.E) / (d.piT u : d.host.E)
  clsLat := fun u i c => d.clsLat u i c
  fm := fun u => d.forms a u

end ColDat

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ}

theorem qth_ext_close (g : Sp E n ≃ₗ[E] Sp E n) (N : ℕ) (hg : lqPrinc P N g) (i l : Fin (n + c)) :
    P.valuation E ((((toGLm E (n + c) (twZrExt (c := c) g) : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) - 1) i l) ≤
      WithZero.exp (-(N : ℤ)) := by
  have hcoe : ∀ W : Sp E (n + c) ≃ₗ[E] Sp E (n + c),
      ((toGLm E (n + c) W : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) =
        LinearMap.toMatrix' (W : Sp E (n + c) →ₗ[E] Sp E (n + c)) := by
    intro W
    simp only [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv,
      MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
      Units.coe_map, MonoidHom.coe_coe]
    rfl
  set u : Fin (n + c) → E := Pi.single l 1 with hu0
  have hpi : ∀ y : Fin n → E, (Loc.inX E n c y) i = if h : (i : ℕ) < n then y ⟨i, h⟩ else 0 := by
    intro y
    simp only [Loc.inX, LinearMap.pi_apply]
    split_ifs <;> rfl
  have hval : ((twZrExt (c := c) g) u) i =
      Loc.inX E n c (g (LinearMap.funLeft E E (Fin.castAdd c) u)) i +
        (u i - Loc.inX E n c (LinearMap.funLeft E E (Fin.castAdd c) u) i) := by
    rw [twZrExt_apply]
    rfl
  rw [hcoe, Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, ← hu0, hval, hpi, hpi]
  by_cases hi : (i : ℕ) < n
  · rw [dite_eq_left hi, dite_eq_left hi]
    have hu : (LinearMap.funLeft E E (Fin.castAdd c)) u ⟨i, hi⟩ = u i := rfl
    rw [hu, sub_self, add_zero]
    by_cases hl : (l : ℕ) < n
    · have hu' : LinearMap.funLeft E E (Fin.castAdd c) u = Pi.single (⟨l, hl⟩ : Fin n) 1 := by
        ext j
        simp [hu0, LinearMap.funLeft_apply, Pi.single_apply, Fin.ext_iff]
      rw [hu']
      have h1 : (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l =
          (1 : Matrix (Fin n) (Fin n) E) ⟨i, hi⟩ ⟨l, hl⟩ := by
        simp [Matrix.one_apply, Fin.ext_iff]
      rw [h1]
      have h2 := hg ⟨i, hi⟩ ⟨l, hl⟩
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe] at h2
      exact h2
    · have hu' : LinearMap.funLeft E E (Fin.castAdd c) u = 0 := by
        ext j
        simp only [hu0, LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Function.comp_apply]
        rw [if_neg]
        intro h
        apply hl
        rw [← h]
        exact j.isLt
      have h1 : (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l = 0 := by
        rw [Matrix.one_apply_ne]
        intro h
        apply hl
        rw [← h]
        exact hi
      rw [hu', map_zero, Pi.zero_apply, h1, sub_zero, map_zero]
      exact zero_le'
  · rw [dite_eq_right hi, dite_eq_right hi, zero_add, sub_zero]
    have h3 : u i - (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l = 0 := by
      simp [hu0, Pi.single_apply, Matrix.one_apply]
    rw [h3, map_zero]
    exact zero_le'

theorem qth_princ_inv {N : ℕ} (g : ↥(GLint E n P)) (hg : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n)) :
    lqPrinc P N ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
  unfold lqPrinc at hg ⊢
  intro i j
  set A := LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hA
  set B := LinearMap.toMatrix'
    ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have hc : ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).comp
        ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      have hx : ((((g⁻¹ * g : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n)) x = x := by
        rw [inv_mul_cancel]
        rfl
      exact hx
    rw [hc, LinearMap.toMatrix'_id]
  have hBle : ∀ a k, P.valuation E (B a k) ≤ 1 := by
    intro a k
    rw [hB, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    have hs : (Pi.single k (1 : E) : Sp E n) ∈ stdAt E n P := by
      show _ ∈ localization₂ P.asIdeal (stdLat E n)
      rw [mem_localization_standardLattice]
      intro t
      rw [qth_intAt_iff]
      by_cases h : t = k
      · subst h
        simp
      · simp [Pi.single_apply, h]
    have hmem : ((g⁻¹ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (stdAt E n P) :=
      (g⁻¹ : GLint E n P).2
    have h2 := ((ChainCounts.mem_stabL_iff.1 hmem) _).2 hs
    have h3 := (mem_localization_standardLattice P _).1 h2 a
    rw [qth_intAt_iff] at h3
    exact h3
  have hBm : B - 1 = -(B * (A - 1)) := by
    rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]
  rw [hBm, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ (fun k _ => ?_)
  rw [map_mul]
  calc _ ≤ 1 * P.valuation E ((A - 1) k j) := mul_le_mul' (hBle i k) le_rfl
    _ ≤ _ := by rw [one_mul]; exact hg k j

end Ext

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Stmt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

def TargetEquivarianceAtPrime (i : ℕ) (w : rowSG Pr sel mu) (hal : AutY X R i) (hbe : AutY X R (i + 1)) : Prop :=
  ∀ r' ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) w.1) hbe, ∀ c' ∈ GLint X.E (R.N (i + 1)) w.1,
    (∀ x, r' (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) (c' x)) →
    ∀ y : HomE X.E (R.N i) (R.N (i + 1)),
      rhoT Ch sel mu i w ((LinearEquiv.det c'⁻¹ : X.Eˣ) : X.E) * E1at Ch sel mu cst i w hal hbe (c'.toLinearMap ∘ₗ y) =
        chiInv Ch sel mu cst (i + 1) w hbe r' * E1at Ch sel mu cst i w hal hbe y

def TargetEquivarianceLargeDepths (i : ℕ) (w : rowSG Pr sel mu) (hal : AutY X R i) (hbe : AutY X R (i + 1)) : Prop :=
  ∃ A₀ B₀ : ℕ, ∀ A' B', A₀ ≤ A' → B₀ ≤ B' → TargetEquivarianceAtPrime Ch sel mu { cst with A := A', B := B' } i w hal hbe

end Stmt

section Assembly

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end Assembly

section Res

variable {k : Type} [Field k] {n c : ℕ}

theorem clXQ_eq_inX {v : Fin (n + c) → k} (hv : v ∈ Loc.Ufl k n c 0) : v = Loc.inX k n c (twZrPr v) := by
  funext l
  unfold Loc.inX
  by_cases h : l.1 < n
  · simp only [LinearMap.pi_apply, dif_pos h, LinearMap.proj_apply]
    rfl
  · simp only [LinearMap.pi_apply, dif_neg h, LinearMap.zero_apply]
    exact hv l (by simpa using h)

theorem clXQ_res {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.R1 k n c) :
    ∃ g : (Fin n → k) ≃ₗ[k] (Fin n → k), ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x) := by
  have h1 : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (twZrPr (r (Loc.inX k n c x))) :=
    fun x => clXQ_eq_inX (hr.1.1 0 _ (twZr_inX_mem_Ufl x 0))
  have h2 : ∀ x, r⁻¹ (Loc.inX k n c x) = Loc.inX k n c (twZrPr (r⁻¹ (Loc.inX k n c x))) :=
    fun x => clXQ_eq_inX (hr.2.1 0 _ (twZr_inX_mem_Ufl x 0))
  refine ⟨LinearEquiv.ofLinear (twZrPr ∘ₗ r.toLinearMap ∘ₗ Loc.inX k n c) (twZrPr ∘ₗ (r⁻¹).toLinearMap ∘ₗ Loc.inX k n c) ?_ ?_, h1⟩
  · refine LinearMap.ext fun x => ?_
    show twZrPr (r (Loc.inX k n c (twZrPr (r⁻¹ (Loc.inX k n c x))))) = x
    rw [← h2]
    show twZrPr (r (r.symm (Loc.inX k n c x))) = x
    rw [LinearEquiv.apply_symm_apply, twZrPr_inX]
  · refine LinearMap.ext fun x => ?_
    show twZrPr (r⁻¹ (Loc.inX k n c (twZrPr (r (Loc.inX k n c x))))) = x
    rw [← h1]
    show twZrPr (r.symm (r (Loc.inX k n c x))) = x
    rw [LinearEquiv.symm_apply_apply, twZrPr_inX]

end Res

section Chr

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)}

theorem clXQ_rhoT_ne (i : ℕ) (w : rowSG Pr sel mu) {n : ℕ} {c : Sp X.E n ≃ₗ[X.E] Sp X.E n} (hc : c ∈ GLint X.E n w.1) :
    rhoT Ch sel mu i w ((LinearEquiv.det c : X.Eˣ) : X.E) ≠ 0 := by
  unfold rhoT
  exact clX_unitV_ne _ (isUnit_reduction_of_integralAt_inv (intAt_det c hc) (intAt_det_inv c hc) (Units.ne_zero _))

theorem clXQ_rhoT_mul (i : ℕ) (w : rowSG Pr sel mu) {n : ℕ} {c c' : Sp X.E n ≃ₗ[X.E] Sp X.E n} (hc' : c' ∈ GLint X.E n w.1) :
    rhoT Ch sel mu i w ((LinearEquiv.det (c * c') : X.Eˣ) : X.E) =
      rhoT Ch sel mu i w ((LinearEquiv.det c : X.Eˣ) : X.E) * rhoT Ch sel mu i w ((LinearEquiv.det c' : X.Eˣ) : X.E) := by
  unfold rhoT
  rw [map_mul, Units.val_mul]
  exact unitV_mul_unit _ (intAt_det c' hc') (intAt_det_inv c' hc') (Units.ne_zero _) _

theorem clXQ_chrOk {i : ℕ} {w : rowSG Pr sel mu} {hal : AutY X R i} {h : AutY X R (i + 1)}
    (hint : prCat (Pr := Pr) cst.sharp (i + 1) w.1 h ≤ GLint X.E (R.N (i + 1)) w.1)
    (hT : TargetEquivarianceLargeDepths Ch sel mu cst i w hal h) (hne : FiniteSumNonzeroLargeDepth Ch sel mu cst i w hal h) : TwChrOk Ch sel mu cst (i + 1) w h := by
  obtain ⟨A₀, B₀, hT⟩ := hT
  obtain ⟨A₁, B₁, hne⟩ := hne
  have T := hT (max A₀ A₁) (max B₀ B₁) (le_max_left _ _) (le_max_left _ _)
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 (hne (max A₀ A₁) (max B₀ B₁) (le_max_right _ _) (le_max_right _ _))
  have hres : ∀ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) w.1) h, ∃ c ∈ GLint X.E (R.N (i + 1)) w.1,
      ∀ x, r (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) (c x) := by
    intro r hr
    obtain ⟨c, hc⟩ := clXQ_res (Subgroup.mem_inf.1 hr).1
    exact ⟨c, hint ⟨r, hr, hc⟩, hc⟩
  refine ⟨fun r hr h0 => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · obtain ⟨c, hc, hcx⟩ := hres r hr
    have e := T r hr c hc hcx ((c⁻¹).toLinearMap ∘ₗ y₀)
    have h0' : chiInv Ch sel mu { cst with A := max A₀ A₁, B := max B₀ B₁ } (i + 1) w h r = 0 := h0
    rw [h0', zero_mul] at e
    have e2 : c.toLinearMap ∘ₗ (c⁻¹).toLinearMap ∘ₗ y₀ = y₀ := by
      refine LinearMap.ext fun v => ?_
      show c (c.symm (y₀ v)) = y₀ v
      rw [LinearEquiv.apply_symm_apply]
    rw [e2] at e
    rcases mul_eq_zero.1 e with e | e
    · exact clXQ_rhoT_ne i w ((GLint X.E (R.N (i + 1)) w.1).inv_mem hc) e
    · exact hy₀ e
  · obtain ⟨c, hc, hcx⟩ := hres r hr
    obtain ⟨c', hc', hcx'⟩ := hres r' hr'
    have hcx'' : ∀ x, r'' (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) ((c * c') x) := by
      intro x
      rw [hx, hcx', hcx]
      rfl
    have e'' := T r'' hr'' (c * c') ((GLint X.E (R.N (i + 1)) w.1).mul_mem hc hc') hcx'' y₀
    have e := T r hr c hc hcx (c'.toLinearMap ∘ₗ y₀)
    have e' := T r' hr' c' hc' hcx' y₀
    have e3 : (c * c').toLinearMap ∘ₗ y₀ = c.toLinearMap ∘ₗ c'.toLinearMap ∘ₗ y₀ := rfl
    rw [e3, mul_inv_rev, clXQ_rhoT_mul i w ((GLint X.E (R.N (i + 1)) w.1).inv_mem hc), mul_assoc, e, ← mul_assoc,
      mul_comm (rhoT Ch sel mu i w _), mul_assoc, e', ← mul_assoc] at e''
    exact (mul_right_cancel₀ hy₀ e'').symm

end Chr

end Formalism.L2.Col
end
end
