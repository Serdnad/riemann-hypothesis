module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Core (D : D7) : Type 1 where
  Q : Par D
  U : ∀ j (σ : Q.c.F →+* ℂ), Unf (Q.Xo j) Q.c σ D.R.r
  V : ℕ → (Q.c.F →+* ℂ) → HSp D
  dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r
  mu : ∀ j σ, GA D (V j σ) → ℂ
  Kf : ∀ j σ, Subgroup (GA D (V j σ))
  pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)

variable {D : D7}

def latHat (V : HSp D) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ a : Af D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) ∧
    ∃ x ∈ V.L0, z = fun i => a ⊗ₜ V.frame.repr x i}

def IsLevelK (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y

def xiR (D : D7) : ℝ := ‖D.host.φ₀ D.host.xi0‖

namespace Core

variable (T : Core D)

def σ₀ : T.Q.c.F →+* ℂ := T.Q.c.F.val.toRingHom

theorem good_σ₀ : GoodEmb T.Q.c T.σ₀ := rfl

abbrev R (j : ℕ) : Type := Rul (T.Q.Xo j) T.Q.c

abbrev cuspA (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule T.Q.c.F (T.R j) :=
  cusp (T.Q.Xo j) T.Q.c (T.U j) a n

abbrev X₀ (j : ℕ) : (T.U j T.σ₀).Comp → Data D.host.E D.R.r := (T.U j T.σ₀).X

def frI (_T : Core D) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := 1

abbrev PtM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def nrmM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) : ℝ := nrmOf la (y.1 f)

theorem nrmM_le_one_iff (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) :
    T.nrmM j la y f ≤ 1 ↔ 0 ≤ y.1 f := by
  unfold nrmM nrmOf
  have hy := y.2
  unfold valSet at hy
  obtain ⟨x, hx⟩ := hy
  unfold vAtV at hx
  obtain ⟨T1, io, e, -, y', -, eta, -, hxe⟩ := x.2
  rw [hxe] at hx
  unfold profI at hx
  have key : y.1 f = nval T1.V e (evI y' f) := by rw [← hx]
  unfold nval at key
  have hN : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    have h1 : Ideal.absNorm la.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact la.isPrime.ne_top
    exact_mod_cast (by omega : 1 < Ideal.absNorm la.asIdeal)
  rw [key]
  by_cases hz : evI y' f = 0
  · simp [hz]
  · simp only [hz, if_false, EReal.coe_ne_top, EReal.toReal_coe, EReal.coe_nonneg]
    constructor
    · intro h
      by_contra hneg
      exact absurd h (not_le.mpr (Real.one_lt_rpow hN (neg_pos.mpr (not_le.mp hneg))))
    · intro h
      exact Real.rpow_le_one_of_one_le_of_nonpos hN.le (neg_nonpos.mpr h)

def phiAd (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) • adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f)

end Core

structure LawsM (T : Core D) : Prop where

  pins : T.Q.Pins

  half : (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal) ∧
    T.Q.l.Mb = ∏ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

  evalWD : ∀ j, InR D j → EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)

  unf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ)

  unTest : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k x,
    FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) ((T.U j σ).un k x)
  chiTriv : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
    ((T.U j σ).X k).χ (laU (T.U j σ) a n k) γ = 1

  dictU : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (T.V j σ) (T.dict j σ) (T.Kf j σ) th hr

  spaceW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j
  levelK : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsLevelK (T.V j σ) (D.host.g 0 * D.host.g 1) (T.Kf j σ)

  xiAbs : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((T.U j σ).X k).ξ0‖ = xiR D
  muUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuUnit (T.V j σ) (T.dict j σ) (T.mu j σ)
  muCont : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → Continuous (T.mu j σ)
  finVol : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → FinVol (T.V j σ)

  cuspFD : ∀ j, InR D j → CuspFD (T.Q.Xo j) T.Q.c (T.U j)

  supDef : ∀ j, InR D j → SupDef (T.Q.Xo j) T.Q.c (T.U j)

  cuspidalL2Subspace : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ)
  l2Def : ∀ j (hj : InR D j) σ (hσ : GoodEmb T.Q.c σ),
    L2DefiniteCuspForms (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) (cuspidalL2Subspace j hj σ hσ)

  unitIndep : ∀ j, InR D j → UnitIndep (T.Q.Xo j) T.Q.c
  ptNe : ∀ j, InR D j → IntFrNe (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)

structure LawsCore (T : Core D) : Prop extends LawsM T where

  cuspMul : ∀ j, InR D j → CuspMul (T.Q.Xo j) T.Q.c (T.U j)

  latZ : ∀ j, InR D j → FJ.LatZ (T.X₀ j) (WeightFamilies.rho D j)
  cuNe : ∀ j, InR D j → FJ.CuNeF (T.X₀ j) (WeightFamilies.rho D j)
  expo : ∀ j, InR D j → FJ.ExpoMatch (T.X₀ j) T.frI (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {g0 : B.Cusp j wF}

theorem isUnit_toOsK_of_lift {y : PtsG G la → E.Pt' la} (hw : ∀ ζ, FromW ζ (y ζ)) (C : CurveModel G la g0)
    (x : ↥(Frac0 (xplus X E hM) la G.w))
    (hx : ∀ ζ, (hw ζ).toSecPt.lift (x : Lw (xplus X E hM) la G.w) ≠ 0) :
    IsUnit (toOsK (xplus X E hM) la G.w x) := by
  classical
  have : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
    have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
    exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv
  have : IsReduced (OsK (xplus X E hM) la G.w) := by
    have : IsReduced (↥C.A' ⧸ C.JA) := C.red
    exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective
  have : IsArtinianRing (OsK (xplus X E hM) la G.w) := IsArtinianRing.of_finite (Kp (xplus X E hM) la G.N) _
  by_contra hnu
  set a := toOsK (xplus X E hM) la G.w x with ha
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum (OsK (xplus X E hM) la G.w), a ∈ I.asIdeal := by
    obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact ⟨⟨M, hM⟩, haM (Ideal.subset_span rfl)⟩
  let e := IsArtinianRing.equivPi (OsK (xplus X E hM) la G.w)
  set ε := e.symm (Pi.single I 1) with hε
  have hεa : ε * a = 0 := by
    apply e.injective
    rw [map_mul, map_zero, hε, e.apply_symm_apply]
    funext m
    by_cases hm : m = I
    · subst hm
      rw [Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.zero_apply]
      show Ideal.Quotient.mk m.asIdeal a = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hI
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul, Pi.zero_apply]
  have hεε : ε * ε = ε := by
    apply e.injective
    rw [map_mul, hε, e.apply_symm_apply]
    funext m
    by_cases hm : m = I
    · subst hm; rw [Pi.mul_apply, Pi.single_eq_same, one_mul]
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul]
  have hε0 : ε ≠ 0 := by
    intro h
    have h1 := congrArg e h
    rw [hε, e.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 I
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    have h3 : (1 : OsK (xplus X E hM) la G.w) ∈ I.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h2)
    exact I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hint : IsIntegral (Op (xplus X E hM) la G.N) ε := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
    simp [pow_two, hεε]
  let ε' : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) := ⟨ε, hint⟩
  have hnot : ¬ IsUnit (1 - ε') := by
    intro hu
    apply hε0
    have h1 : ε' * (1 - ε') = 0 := by
      apply Subtype.ext
      show ε * (1 - ε) = 0
      rw [mul_sub, mul_one, hεε, sub_self]
    have h2 := (hu.mul_left_eq_zero).1 h1
    exact congrArg Subtype.val h2
  obtain ⟨Z, hZ, hZ1⟩ := Ideal.exists_le_maximal (Ideal.span {1 - ε'}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  let ζ : PtsG G la := ⟨Z, hZ⟩
  have hεZ : ε' ∉ ζ.asIdeal := by
    intro h
    have h1 : (1 - ε') + ε' ∈ Z := Z.add_mem (hZ1 (Ideal.subset_span rfl)) h
    rw [sub_add_cancel] at h1
    exact hZ.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  obtain ⟨e0, he0⟩ := toOsK_surjective (xplus X E hM) la G.w ε
  have hev := (hw ζ).evW e0 ε' he0
  have hu : IsUnit (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ) ε') :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal ε').2 hεZ
  have hne : (hw ζ).toSecPt.lift (e0 : Lw (xplus X E hM) la G.w) ≠ 0 := by
    rw [hev]
    exact ((hu.map (hw ζ).ι).map (algebraMap (hw ζ).T.V (hw ζ).T.Fr)).ne_zero
  have hJ : e0 * x ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_mul, he0]
    exact hεa
  have h0 := (hw ζ).toSecPt.lift_Jid hJ
  rw [Subalgebra.coe_mul, map_mul] at h0
  exact mul_ne_zero hne (hx ζ) h0

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


variable (Xo c) in
def CombAlg {n : ℕ} (ws : Fin n → Rul Xo c) (et : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (c' : ℝ) :
    Prop :=
  ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
    (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v et)


variable (c) in
def nuOf (nus : HeightOneSpectrum (𝓞 c.F) → ℝ) (la : HeightOneSpectrum (𝓞 c.F)) : ℝ :=
  (ramOverZ la : ℝ) * nus la


variable (c) in
def NumericalH1Condition (nus : HeightOneSpectrum (𝓞 c.F) → ℝ) (P s : ℝ) : Prop :=
  (∀ la, 0 ≤ nus la) ∧ (Function.support nus).Finite ∧
    (∑ᶠ la, (ramOverZ la : ℝ) * nus la * logNorm la) / (Module.finrank ℚ c.F : ℝ) ≤ P * s

def OrdTieOn (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 c.F)),
    IsNormDiscrete v → IsOver (K := c.F) v la →
    ∃ y : PtV Xo c cls (PY la) (lies la) la,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) =
          (((ramIdx (K := c.F) v la : ℤ) : ℝ) : EReal) * vAtV y f) ∧
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 →
        (∃ g ∈ sec Xo c a n, evC h Z g ≠ 0) → vAtV y f = ⊤)

theorem OrdTieOn.ordTie {h : GenFrEx Xo c} {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    {cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop} {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (H : OrdTieOn h δ cls PY lies) : OrdTie h δ cls PY lies := fun Z v la hv ho =>
  let ⟨y, hy, _⟩ := H Z v la hv ho
  ⟨y, hy⟩

theorem one_le_ramIdx {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)} (hv : IsNormDiscrete v)
    (ho : IsOver (K := K) v la) : 1 ≤ ramIdx (K := K) v la := by
  unfold ramIdx
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hK : ((a : K)) ≠ 0 := by exact_mod_cast ha0
  have hne : v (algebraMap K Ω (a : K)) ≠ ⊤ := hv.1 _ ((map_ne_zero _).2 hK)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  refine le_csInf ⟨n, a, ha, ha0, hn.symm⟩ ?_
  rintro m ⟨b, hb, _, hbm⟩
  have h1 := (ho b).2 hb
  rw [hbm] at h1
  have h0 : (0 : ℤ) < m := by exact_mod_cast h1
  omega

section H1

variable [Fintype (Comp Xo c)] (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nus : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

theorem height_H1_of_data {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (hreg : regular₂ Xo c U)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2) (hw : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2)
    (he : etR ∈ cusp Xo c U uet.1 uet.2) (hnz : NoCommonZero Xo c wR) (hetZ : NZAt h etR)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (hcomb : CombAlg Xo c wR etR (nuOf c nus) (cc / (2 * (i : ℝ))))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)
    (htie : OrdTieOn h δ cls PY lies) (hnu : NumericalH1Condition c nus PN (wsize (wtZ uL.1 uL.2))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R
      (nuOf c nus) ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).FinitePlaceHyp := by
  classical
  refine ⟨fun la => mul_nonneg (Nat.cast_nonneg _) (hnu.1 la), ?_, hnu.2.2, ?_⟩
  · refine hnu.2.1.subset fun la hla => ?_
    rw [Function.mem_support] at hla ⊢
    intro h0
    apply hla
    show (ramOverZ la : ℝ) * nus la = 0
    rw [h0, mul_zero]
  · intro Z v la hadm hover
    show ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0},
        ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤
      (ramIdx (K := c.F) v la : ℝ) * nuOf c nus la +
        cc / (2 * (i : ℝ)) * (ordC (δ Z v) v ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) : ℝ)
    rw [← huet]
    have hv : IsNormDiscrete v := hadm.1
    obtain ⟨y, hty, hzero⟩ := htie Z v la hv hover
    obtain ⟨T', io, e, ho, z, _, eta, _, hq⟩ := y.2
    let y1 : PtV Xo c (trivialClassCondition Xo c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho z trivial () trivial
    have hyv : vAtV y1 = vAtV y := funext fun g => by
      show y1.1.1 g = y.1.1 g
      rw [hq]
      rfl
    have hc' : (0 : ℝ) ≤ cc / (2 * (i : ℝ)) := div_nonneg hcc (by positivity)
    have hR := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hw k⟩) ⟨etR, he⟩ (nuOf c nus)
      (cc / (2 * (i : ℝ))) hc' hnz (fun la' y0 => hcomb la' y0.1 y0.2)).1 la ⟨vAtV y1, y1, rfl⟩
    have hR' : 0 ≤ vAtV y etR ∧ (vAtV y etR ≠ ⊤ →
        (⨅ k, vAtV y (wR k)) ≤ ((nuOf c nus la : ℝ) : EReal) + ((cc / (2 * (i : ℝ)) : ℝ) : EReal) * vAtV y etR) := by
      rw [← hyv]
      exact hR
    have he1 : 1 ≤ ramIdx (K := c.F) v la := one_le_ramIdx hv hover
    have hepos : (0 : ℝ) < (ramIdx (K := c.F) v la : ℝ) := by
      exact_mod_cast (show (0 : ℤ) < ramIdx (K := c.F) v la by omega)
    have hE := (hty uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ he) (hetZ Z))
    have htopE : vAtV y etR ≠ ⊤ := by
      intro htop
      rw [htop, EReal.mul_top_of_pos (by exact_mod_cast hepos)] at hE
      exact EReal.coe_ne_top _ hE
    obtain ⟨x, hx⟩ : ∃ x : ℝ, vAtV y etR = (x : EReal) :=
      ⟨_, (EReal.coe_toReal htopE (vAtV_ne_bot y etR)).symm⟩
    have hB := hR'.2 htopE
    rw [hx, ← EReal.coe_mul, ← EReal.coe_add] at hB
    rw [hx, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at hE
    obtain ⟨k0, hk0⟩ : ∃ k0, vAtV y (wR k0) = ⨅ k, vAtV y (wR k) := exists_eq_ciInf_of_finite
    rw [← hk0] at hB
    have hk0Z : evC h Z (wR k0) ≠ 0 := by
      intro h0
      rw [hzero uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hw k0)) h0
        ⟨wR (jc Z), cusp_le_sec Xo c U _ _ (hw (jc Z)), hwb Z⟩] at hB
      exact absurd hB (not_le.2 (EReal.coe_lt_top _))
    have hW := hty uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hw k0)) hk0Z
    have htopW : vAtV y (wR k0) ≠ ⊤ := fun ht => by
      rw [ht] at hB
      exact absurd hB (not_le.2 (EReal.coe_lt_top _))
    obtain ⟨t, ht⟩ : ∃ t : ℝ, vAtV y (wR k0) = (t : EReal) :=
      ⟨_, (EReal.coe_toReal htopW (vAtV_ne_bot y _)).symm⟩
    rw [ht, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at hW
    rw [ht, EReal.coe_le_coe_iff] at hB
    calc ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0},
          ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ)
        ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) :=
          Int.cast_le.2 (ciInf_le (f := fun j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0} =>
            ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) (Set.finite_range _).bddBelow
            ⟨k0, valC_ne_zero (a := uL.1) (n := uL.2) hk0Z⟩)
      _ = (ramIdx (K := c.F) v la : ℝ) * t := hW
      _ ≤ (ramIdx (K := c.F) v la : ℝ) * (nuOf c nus la + cc / (2 * (i : ℝ)) * x) :=
          mul_le_mul_of_nonneg_left hB hepos.le
      _ = (ramIdx (K := c.F) v la : ℝ) * nuOf c nus la +
            cc / (2 * (i : ℝ)) * ((ramIdx (K := c.F) v la : ℝ) * x) := by ring
      _ = _ := by rw [← hE]

end H1

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def colR (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (j : Fin r) : ℝ :=
  ‖dmin X.Gm x τ j.succ / dmin X.Gm x τ j.castSucc‖


def IsIdOrConj {σ σ' : c.F →+* ℂ} (φ : CAt σ →ₐ[c.F] CAt σ') : Prop :=
  (∀ z : CAt σ, toC (φ z) = toC z) ∨ ∀ z : CAt σ, toC (φ z) = starRingEnd ℂ (toC z)

def RdAt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ))
    (q : Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ)) : Prop :=
  ∃ (y' : FrPt Xo c (CAt (goodOf c σ))) (φ : CAt σ →ₐ[c.F] CAt (goodOf c σ)),
    IsIdOrConj φ ∧ FrMap φ y y' ∧ FrBor q.2.2 ((U (goodOf c σ)).un q.1 q.2.1) y'



variable (Xo c) in
def CBaseEx (h : GenFrEx Xo c) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ y : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) y

def yPDef (h : GenFrEx Xo c) (hb : CBaseEx Xo c h) (Z : Comp Xo c) (P : Om Z →+* ℂ) : FrPt Xo c (CAt (sgOf P)) :=
  (hb Z P).choose

end Formalism.L2.Pj
end
end
