module

public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle139
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.Mem.SJ.Place

theorem exists_tw_extend {H K X : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (V : Submodule ℂ X) (φ : V →ₗ⋆[ℂ] K) (z : ℂ) (s : Bool) :
    ∃ sE : Tw s H →ₗ⋆[ℂ] Tw s K, ∀ (x : Tw s H) (hx : e (Tw.out x) ∈ V), sE x = Tw.mk s (z • φ ⟨e (Tw.out x), hx⟩) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V.comap e) (e.restrict (p := V.comap e) (q := V) fun _ h => h)
  refine ⟨{ toFun := fun x => Tw.mk s (z • φ (g (Tw.out x))), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    show z • φ (g (Tw.out x + Tw.out y)) = z • φ (g (Tw.out x)) + z • φ (g (Tw.out y))
    rw [map_add (f := _), map_add (f := _), smul_add]
  · intro a x
    show z • φ (g (cj s a • Tw.out x)) = cj s (starRingEnd ℂ a) • z • φ (g (Tw.out x))
    rw [map_smul, map_smulₛₗ, cj_conj, smul_comm]
  · intro x hx
    have := LinearMap.congr_fun hg ⟨Tw.out x, hx⟩
    show Tw.mk s (z • φ (g (Tw.out x))) = _
    rw [show g (Tw.out x) = ⟨e (Tw.out x), hx⟩ from this]

theorem scale_norm {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {c n a : ℝ} (hc : 0 < c) (hn : 0 < n) (y : K)
    (h : ‖y‖ ^ 2 = c * a) : n * ‖((1 : ℂ) * (((Real.sqrt (c * n))⁻¹ : ℝ) : ℂ)) • y‖ ^ 2 = a := by
  have hcn : 0 < c * n := mul_pos hc hn
  rw [one_mul, norm_smul, Complex.norm_real, mul_pow, h, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hcn.le]
  field_simp

theorem sEEofTT_spec {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0)))
    (𝓕 : Set (GA D (D.sp.Y 0))) (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) (h : EvalTieT M μ 𝓕 E X G ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E X G ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re ∧
      ((sEEofTT M μ 𝓕 E X G ι t c T : HHX X) : L2X X) ∈ goodSub X G := by
  have e : sEEofTT M μ 𝓕 E X G ι t c = (conjHH X G).toLinearMap.comp h.choose_spec.2.choose.toLinearMap := by
    unfold sEEofTT
    exact dif_pos h
  have e' : sEEofTT M μ 𝓕 E X G ι t c T = conjHH X G (h.choose_spec.2.choose T) := by
    rw [e]
    rfl
  rw [e']
  refine ⟨?_, (mem_EEC X G _).1 (h.choose_spec.2.choose T).2⟩
  rw [(conjHH X G).norm_map]
  exact (h.choose_spec.2.choose_spec T).2

theorem exists_placement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) (ι : GA D (Yc D 0) ≃* St.B.I.GA) (t : GA D (Yc D 0)) (c : ℝ) (s : Bool), R.models_HE → 0 < c → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c → ∃ (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX St)), 0 < κ ∧ ∀ (x : Tw s R.HE.H) (hx : R.HE.e (Tw.out x) ∈ R.EEat (R.levR F true)), sE x = Tw.mk s (((1 : ℂ) * (κ : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) ∧ RealDat.nP F true * ‖sE x‖ ^ 2 = ‖x‖ ^ 2 ∧ ((Tw.out (sE x) : HHX St) : L2X St) ∈ goodSub St Gd := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F St Gd ι t c s hE hc h
  have hn : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  obtain ⟨sE, hs⟩ := exists_tw_extend R.HE.e (R.EEat (R.levR F true))
    (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c)
    ((1 : ℂ) * (((Real.sqrt (c * RealDat.nP F true))⁻¹ : ℝ) : ℂ)) s
  refine ⟨(Real.sqrt (c * RealDat.nP F true))⁻¹, sE, inv_pos.2 (Real.sqrt_pos.2 (mul_pos hc hn)), fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := sEEofTT_spec (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c h ⟨R.HE.e (Tw.out x), hx⟩
  refine ⟨hs x hx, ?_, ?_⟩
  · rw [hs x hx]
    have hip : (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2 := by
      rw [← hE.2.2]
      exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (Tw.out x)).symm
    have key := scale_norm (K := HHX St) hc hn
      (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) (h1.trans (congrArg (c * ·) hip))
    exact key
  · rw [hs x hx]
    exact (goodSub St Gd).smul_mem _ h2

end GlobalTheory.Mem.SJ.Place
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalChoice

theorem exists_pin (P : ℝ → Prop) (h : ∀ a b, P a → P b → a = b) : ∃ a, ∀ l, P l → a = l := by
  by_cases hP : ∃ a, P a
  · obtain ⟨a, ha⟩ := hP
    exact ⟨a, fun l hl => h a l ha hl⟩
  · exact ⟨0, fun l hl => absurd ⟨l, hl⟩ hP⟩

theorem exists_eig {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (f : M → M) (c : ℝ) :
    ∃ a : ℝ, (∀ l : ℝ, S ≠ ⊥ → (∀ x ∈ S, f x = (l : ℂ) • x) → a = l) ∧ (S = ⊥ → a = c) := by
  rcases eq_or_ne S ⊥ with hW | hW
  · exact ⟨c, fun l h => absurd hW h, fun _ => rfl⟩
  · obtain ⟨a, ha⟩ := exists_pin (fun l => ∀ x ∈ S, f x = (l : ℂ) • x) (fun a b ha hb => by
        obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
        exact_mod_cast smul_left_injective ℂ hx0 ((ha x hx).symm.trans (hb x hx)))
    exact ⟨a, fun l _ h => ha l h, fun h => absurd h hW⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev withScal (R : RealDat D A Ks) (lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (kap : ℝ) :
    RealDat D A Ks := { R with lam := lam, kap := kap }

def OffEq (R : RealDat D A Ks) (F : Face D A) (b : Bool) (i : Fin D.R.m) (p : A.fam.base.Ix)
    (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  ∀ x, (R.toCx F).tC F.cr b i A.μ0 (Cx.cpt A.v0.embedding x) ∈ (R.toCx F).Wp i p → ∀ y,
      inner ℂ ((R.toCx F).wC b i v (Cx.cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec x)))
          ((R.toCx F).wC b i v (Cx.cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec y))) =
        ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((Cx.lv (F.fc (R.toCx F).zs) b).XT i A.μ0) v x y

theorem OffEq.unique {R : RealDat D A Ks} {F : Face D A} {b : Bool} {i : Fin D.R.m} {p : A.fam.base.Ix}
    {v : InfinitePlace D.what₂.LL} {l l' : ℝ} (hp : R.PartAt F b i p v) (h : OffEq R F b i p v l)
    (h' : OffEq R F b i p v l') : l = l' := by
  obtain ⟨x, hx, hx0⟩ := hp
  have h1 := (h x hx x).symm.trans (h' x hx x)
  have h2 := mul_right_cancel₀ (by exact_mod_cast hx0) h1
  exact_mod_cast h2

theorem partAt_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) (b i p v) :
    (withScal R lam kap).PartAt F b i p v ↔ R.PartAt F b i p v := Iff.rfl

theorem offEq_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) (b i p v l) :
    OffEq (withScal R lam kap) F b i p v l ↔ OffEq R F b i p v l := Iff.rfl

theorem exists_thetaLift_adjoint_scalar_on_part (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (p : A.fam.base.Ix) (c : ℝ) :
    ∃ a : ℝ, (∀ l : ℝ, R.Wp i p ≠ ⊥ →
      (∀ x ∈ R.Wp i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) → a = l) ∧ (R.Wp i p = ⊥ → a = c) :=
  exists_eig (R.Wp i p) (fun x => R.thG i t (LinearMap.adjoint (R.thG i t) x)) c

theorem exists_lamOff (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (p : A.fam.base.Ix)
    (v : InfinitePlace D.what₂.LL) (c : ℝ) :
    ∃ a : ℝ, (∀ b (l : ℝ), R.PartAt F b i p v → (b = false ∨ ¬ R.PartAt F false i p v) → OffEq R F b i p v l → a = l) ∧
      ((∀ b, ¬ R.PartAt F b i p v) → a = c) := by
  by_cases h0 : R.PartAt F false i p v
  · obtain ⟨a, ha⟩ := exists_pin (OffEq R F false i p v) (fun a b => OffEq.unique h0)
    refine ⟨a, fun b l _ hb h => ?_, fun h => absurd h0 (h false)⟩
    rcases hb with rfl | hb
    · exact ha l h
    · exact absurd h0 hb
  · by_cases h1 : R.PartAt F true i p v
    · obtain ⟨a, ha⟩ := exists_pin (OffEq R F true i p v) (fun a b => OffEq.unique h1)
      refine ⟨a, fun b l hp _ h => ?_, fun h => absurd h1 (h true)⟩
      cases b
      · exact absurd hp h0
      · exact ha l h
    · refine ⟨c, fun b l hp _ _ => ?_, fun _ => rfl⟩
      cases b
      · exact absurd hp h0
      · exact absurd hp h1

theorem exists_isScal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, ∃ lam kap, ({ R with lam := lam, kap := kap } : RealDat D A Ks).IsScal F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F
  classical
  choose f0 hf0 hf0' using fun i t p => exists_thetaLift_adjoint_scalar_on_part R i t p (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  choose f1 hf1 hf1' using fun i p v => exists_lamOff R F i p v (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  obtain ⟨lam, h0, h1⟩ : ∃ lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ,
      (∀ i t p, lam i t p A.v0 = f0 i t p) ∧ ∀ i t p v, v ≠ A.v0 → lam i t p v = f1 i p v :=
    ⟨fun i t p v => if v = A.v0 then f0 i t p else f1 i p v, fun i t p => if_pos rfl, fun i t p v hv => if_neg hv⟩
  obtain ⟨kap, hk⟩ := exists_pin (fun κ => Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp
      (withScal R lam 0).lamN κ ∧ ∃ t p, R.EEp p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (withScal R lam 0).lamN t j p ≠ 0)
    (fun a b ha hb => by
      obtain ⟨t, p, hp, hl⟩ := ha.2
      exact Lift.IsKap.unique ha.1 hb.1 t p hp hl)
  refine ⟨lam, kap, (?_ : (withScal R lam kap).IsScal F)⟩
  refine ⟨fun i t p l hW h => ?_, fun κ h h' => hk κ ⟨h, h'⟩, fun b i p v l hv hp hb h => ?_, fun i t p hW => ?_,
    fun i p v hv h => ?_, fun i t p v hv => ?_⟩
  · exact (h0 i t p).trans (hf0 i t p l hW h)
  · refine (h1 i _ p v hv).trans (hf1 i p v b l ((partAt_withScal R F lam kap b i p v).1 hp) ?_
      ((offEq_withScal R F lam kap b i p v l).1 h))
    rwa [partAt_withScal] at hb
  · exact (h0 i t p).trans (hf0' i t p hW)
  · exact (h1 i _ p v hv).trans (hf1' i p v fun b hb => h b ((partAt_withScal R F lam kap b i p v).2 hb))
  · exact (h1 i t p v hv).trans (h1 i _ p v hv).symm

end GlobalTheory.ScalChoice
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace GlobalTheory.DefLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Poly

variable {ι : Type} {m n : ℕ}

abbrev Pol (ι : Type) (m n : ℕ) : Type := MvPolynomial (ι × Fin m × Fin n) ℂ

def subst (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) : Pol ι m n →ₐ[ℂ] Pol ι m n :=
  MvPolynomial.aeval fun v => ∑ i, ∑ c, (b v.1 i v.2.1 * a v.1 v.2.2 c) • MvPolynomial.X (v.1, i, c)


open Classical in
def rowSub (n : ℕ) (τ : ι) (u : Matrix.unitaryGroup (Fin m) ℂ) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  (subst (fun _ => 1) (fun ρ => if ρ = τ then (u : Matrix (Fin m) (Fin m) ℂ) else 1)).toLinearMap


open Classical in
def colSub (m : ℕ) (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  (subst (fun ρ => if ρ = τ then star (g : Matrix (Fin n) (Fin n) ℂ) else 1) (fun _ => 1)).toLinearMap

def rowLie (n : ℕ) (τ : ι) (k l : Fin m) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  ∑ c : Fin n, LinearMap.mulLeft ℂ (MvPolynomial.X (τ, k, c)) ∘ₗ (MvPolynomial.pderiv (τ, l, c)).toLinearMap

def colLie (m : ℕ) (τ : ι) (k l : Fin n) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  ∑ i : Fin m, LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, k)) ∘ₗ (MvPolynomial.pderiv (τ, i, l)).toLinearMap

theorem rowLie_apply (τ : ι) (k l : Fin m) (P : Pol ι m n) :
    rowLie n τ k l P = ∑ c : Fin n, MvPolynomial.X (τ, k, c) * MvPolynomial.pderiv (τ, l, c) P := by
  simp [rowLie, LinearMap.sum_apply]

theorem colLie_apply (τ : ι) (k l : Fin n) (P : Pol ι m n) :
    colLie m τ k l P = ∑ i : Fin m, MvPolynomial.X (τ, i, k) * MvPolynomial.pderiv (τ, i, l) P := by
  simp [colLie, LinearMap.sum_apply]

end Poly

def IrrFam {ι κ X : Type} [AddCommGroup X] [Module ℂ X] (π : ι → κ → Module.End ℂ X) : Prop :=
  ∀ U : Submodule ℂ X, (∀ τ u, ∀ x ∈ U, π τ u x ∈ U) → U = ⊥ ∨ U = ⊤

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def AllPlus (M : DSModel V S) : Prop := ∀ τ a, M.ε τ a = true

def unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (M.fr τ)⁻¹ * u * M.fr τ

def IsTensAct (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) : Prop :=
  ∀ τ u x, inclT M (π τ u x) = actT M τ (unfr M τ u) (inclT M x)

variable {M : DSModel V S}

theorem AllPlus.jm (h : AllPlus M) (τ : D.what₂.Tau) : Formalism.REAL.Jm (M.ε τ) = 1 := by
  unfold Formalism.REAL.Jm
  simp [h τ]

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

theorem AllPlus.gram (h : AllPlus M) (τ : D.what₂.Tau) : gramAt D V τ = (M.fr τ)ᴴ * M.fr τ := by
  rw [← M.fr_gram τ, h.jm, Matrix.mul_one]

theorem AllPlus.posDef (h : AllPlus M) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  rw [h.gram]
  exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (M.fr_unit τ))

theorem AllPlus.cart (h : AllPlus M) (τ : D.what₂.Tau) : cart M τ = 1 := by
  unfold Links.cart
  rw [h.jm, Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem fr_unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.fr τ * unfr M τ u * (M.fr τ)⁻¹ = u := by
  unfold unfr
  rw [Matrix.mul_assoc (M.fr τ)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (fr_det M τ),
    Matrix.mul_nonsing_inv_cancel_right _ _ (fr_det M τ)]

theorem rep_unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.rep τ (unfr M τ u) = M.σ τ u := by
  unfold DSModel.rep
  rw [fr_unfr]

theorem AllPlus.unfr_mem (h : AllPlus M) (τ : D.what₂.Tau) (u : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    unfr M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hu : (u : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
  have e : M.fr τ * unfr M τ u = u * M.fr τ := by
    unfold unfr
    rw [Matrix.mul_assoc (M.fr τ)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (fr_det M τ)]
  show (unfr M τ u)ᴴ * gramAt D V τ * unfr M τ u = gramAt D V τ
  rw [h.gram]
  calc _ = (M.fr τ * unfr M τ u)ᴴ * (M.fr τ * unfr M τ u) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * ((u : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * u) * M.fr τ := by
      rw [e]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hu, Matrix.mul_one]

theorem AllPlus.exists_unfr (h : AllPlus M) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : ∃ u : Matrix.unitaryGroup (Fin V.rank) ℂ, unfr M τ u = g := by
  have hg' : gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g = (M.fr τ)ᴴ * M.fr τ := by rw [← h.gram]; exact hg
  refine ⟨⟨M.fr τ * g * (M.fr τ)⁻¹, Matrix.mem_unitaryGroup_iff'.2 ?_⟩, ?_⟩
  · calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * (M.fr τ * (M.fr τ)⁻¹) := by
          rw [hg']; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ (fr_det M τ)]; simp
  · show (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ = g
    rw [Matrix.mul_assoc (M.fr τ), Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M τ),
      Matrix.nonsing_inv_mul_cancel_right _ _ (fr_det M τ)]

end Model

end GlobalTheory.DefLift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultAction

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
  (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

abbrev MultP : Submodule ℂ (MMap M) := Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L))

variable {θ M β L}

theorem hasType {U : MMap M} (hU : U ∈ MultP θ M β L) (v : M.Vec) : HasType V β (flag1L L) (U v) :=
  fun κ hκ y => ((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ U).1 hU).lev v κ hκ y

theorem isMultMap_translate {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (h : IsMultMap θ M J χ T) {k : GA D V}
    (hk : k ∈ GfC V) : IsMultMap θ M ∅ χ (heckeOn M {k} T) := by
  have e : ∀ v, heckeOn M {k} T v = rTr V k (T v) := fun v => by
    funext g
    simp [heckeOn, postOn_apply, heckeLin_apply, rTr]
  refine ⟨fun v => ?_, fun v => ?_, fun v k hk => hk.elim, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    exact GlobalTheory.FinTranslate.isAutFunSm_rTr θ V k hk _ (h.aut v)
  · rw [e]
    intro r C hC μ 𝓕 hμ h𝓕 g
    simp only [rTr, mul_assoc]
    exact h.cusp v r C hC μ 𝓕 hμ h𝓕 (g * k)
  · rw [e, e, h.equiv τ g hg v w hw]
    funext x
    unfold rTr
    rw [mul_assoc, mul_assoc, GlobalTheory.FinTranslate.comm_fin_real V hk (GlobalTheory.FinTranslate.atTau_mem θ V τ g)]
  · obtain ⟨ℓ, s, e'⟩ := h.cont τ v (x * k)
    exact ⟨ℓ, s, fun w => by rw [e, e']; rfl⟩

theorem exists_principalLevelMultiplicity_finiteGroup_image (g0 : G0 L.Pg L.r) (T : MMap M) (hT : T ∈ MultP θ M β L) :
    ∃ T' ∈ MultP θ M β L, ∀ v, T' v = actG0 V β L g0 (T v) := by
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hk.choose_spec
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT
    have hact : ∀ v, ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) v =
        actG0 V β L g0 (T v) := by
      intro v
      unfold actG0
      rw [dite_eq_left hk]
      funext g
      simp [heckeOn, postOn_apply, heckeLin_apply]
    have h0 : IsMultMap θ M ∅ (levChi V β (flag1L L))
        ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) := by
      rw [← GlobalTheory.MultMem.mem_mult_iff]
      exact Submodule.smul_mem _ _
        ((GlobalTheory.MultMem.mem_mult_iff ..).2 (isMultMap_translate hT hκ.1))
    refine ⟨_, Submodule.subset_span ⟨h0.aut, h0.cusp, fun v k hk' g => ?_, h0.equiv, h0.cont⟩, hact⟩
    rw [hact]
    exact GlobalTheory.FlagAction.act_hasType (fun k hk => hT.lev v k hk) hk k hk' g
  · refine ⟨0, Submodule.zero_mem _, fun v => ?_⟩
    unfold actG0
    rw [dite_eq_right hk]
    rfl

theorem act_mem (g : G0 L.Pg L.r) {U : MMap M} (hU : U ∈ MultP θ M β L) : postOn M (actL V β L g) U ∈ MultP θ M β L := by
  obtain ⟨U', h1, h2⟩ := exists_principalLevelMultiplicity_finiteGroup_image g U hU
  have h : postOn M (actL V β L g) U = U' := MultilinearMap.ext fun v => (h2 v).symm
  rw [h]
  exact h1

theorem act_one {U : MMap M} (hU : U ∈ MultP θ M β L) : postOn M (actL V β L 1) U = U :=
  MultilinearMap.ext fun v => GlobalTheory.FlagAction.act_one (hasType hU v)

theorem act_mul (hl : LiftsExist V β L) (g g' : G0 L.Pg L.r) {U : MMap M} (hU : U ∈ MultP θ M β L) :
    postOn M (actL V β L (g * g')) U = postOn M (actL V β L g) (postOn M (actL V β L g') U) :=
  MultilinearMap.ext fun v => GlobalTheory.FlagAction.act_mul (hasType hU v) (hl g) (hl g')

variable {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r)

theorem postOn_gaL (c : G → ℂ) (U : MMap M) :
    postOn M (gaL V β L eG c) U = ∑ g, c g • postOn M (actL V β L (eG g)) U := by
  refine MultilinearMap.ext fun v => ?_
  simp only [gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]

theorem gaL_act (hl : LiftsExist V β L) {c : G → ℂ} (hc : ∀ g a, c (g * a * g⁻¹) = c a) (g : G) {U : MMap M}
    (hU : U ∈ MultP θ M β L) :
    postOn M (gaL V β L eG c) (postOn M (actL V β L (eG g)) U) =
      postOn M (actL V β L (eG g)) (postOn M (gaL V β L eG c) U) := by
  have hm : ∀ a b : G, postOn M (actL V β L (eG a)) (postOn M (actL V β L (eG b)) U) =
      postOn M (actL V β L (eG (a * b))) U := fun a b => by
    rw [map_mul]
    exact (act_mul hl _ _ hU).symm

  rw [postOn_gaL, postOn_gaL, map_sum]
  simp only [map_smul, hm]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun a => ?_).symm
  show _ = c (g * a * g⁻¹) • postOn M (actL V β L (eG (g * a * g⁻¹ * g))) U
  rw [hc, inv_mul_cancel_right]


end GlobalTheory.MultAction

end
end
