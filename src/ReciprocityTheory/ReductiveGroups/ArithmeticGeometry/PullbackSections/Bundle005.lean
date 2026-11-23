module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

section Val

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K'] [Algebra V K'] [IsFractionRing V K']

theorem nval_nonneg_of_int (e : ℕ) {x : K'} (hx : x ∈ (algebraMap V K').range) : 0 ≤ nval V e x := by
  unfold nval
  split_ifs with h0
  · exact le_top
  · obtain ⟨y, rfl⟩ := hx
    unfold vV
    have hv : valV V ((algebraMap V K') y) ≤ 1 := by
      unfold valV
      exact HeightOneSpectrum.valuation_le_one _ y
    have hne : valV V ((algebraMap V K') y) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    have hl : ((valV V) ((algebraMap V K') y)).log ≤ 0 := by
      first
      | exact (WithZero.log_le_log hne one_ne_zero).mpr hv |>.trans_eq WithZero.log_one
      | exact WithZero.log_nonpos hv
      | exact WithZero.log_le_zero_iff.mpr hv
      | simpa using WithZero.log_mono hne hv
    have h1 : (0:ℝ) ≤ ((-(valV V ((algebraMap V K') y)).log : ℤ) : ℝ) / (e : ℝ) :=
      div_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ -(valV V ((algebraMap V K') y)).log)) (Nat.cast_nonneg _)
    exact EReal.coe_nonneg.mpr h1

end Val

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def AdaptAt {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ k : ℕ, ((k : 𝓞 K) ∉ la.asIdeal) ∧ Ideal.span {(k : 𝓞 E)} • Λ.La ≤ stdLat E n ∧
    Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ.La

section Ultra

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem le_nval_sum (e : ℕ) {ι : Type} (s : Finset ι) (f : ι → K') (r : EReal) (h : ∀ i ∈ s, r ≤ nval V e (f i)) :
    r ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  unfold nval at h ⊢
  split_ifs with hs
  · exact le_top
  · have hne : s.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty] at hn
      exact hs (by rw [hn, Finset.sum_empty])
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s (fun i => valV V (f i)) hne
    have hle : valV V (∑ i ∈ s, f i) ≤ valV V (f i) := Valuation.map_sum_le _ hmax
    have hfi : f i ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hle
      exact hs ((Valuation.zero_iff _).1 (le_antisymm hle zero_le'))
    have h1 := h i hi
    rw [if_neg hfi] at h1
    refine h1.trans ?_
    have hlog := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs) ((Valuation.ne_zero_iff _).2 hfi)).2 hle
    refine EReal.coe_le_coe_iff.2 ?_
    have hl : ((-(valV V (f i)).log : ℤ) : ℝ) ≤ ((-(valV V (∑ i ∈ s, f i)).log : ℤ) : ℝ) := by
      exact_mod_cast neg_le_neg hlog
    exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg e)

end Ultra

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def FrBCFieldSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (K : Type) [Field K] [Algebra c.F K]
    (ψ : S →ₐ[c.F] K), ∃ z : FrPt Xo c K, FrMap ψ y z

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

def CDVRExtSt : Prop :=
  ∀ (T : CDVR), T.FinRes → ∀ (K : Type) [Field K] (jK : T.Fr →+* K),
    (letI := jK.toAlgebra; FiniteDimensional T.Fr K) →
    ∃ (T' : CDVR) (κ : K →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : T.Fr, a ≠ 0 → vV T'.V (κ (jK a)) = (e' : ℤ) * vV T.V a) ∧ T'.FinRes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IntFrBCSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (yI : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e' : ℕ), 0 < e' →
    (∀ a : T.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV T.V a) →
    ∃ yI' : IntFr Xo c T' (iT.comp io),
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      ∃ φ : T.Fr →ₐ[c.F] T'.Fr, φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

def SecTie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (I : IntData Xo c Tc io yI.1) (k : ℕ)
    (F : letI := io.toAlgebra; LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo yI.1.x)))
    (σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => (k : ℤ)))) : Prop :=
  letI := io.toAlgebra
  ∃ σt : LB.Sec (LB.LinComb I.t'.PP.L (K := Fin 1) (fun _ => 𝟙 I.t'.G.left) (fun _ => (k : ℤ))),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (zp : Z ⟶ Gx yI.1.x),
      zp ≫ (snd (Over.mk yI.1.x) Xo.univ.t.G).left = r ≫ I.m1.φ →
      zp ≫ (fst (Over.mk yI.1.x) Xo.univ.t.G).left = r ≫ I.t'.G.hom →
      ∀ (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
        (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good Xo.univ.t.PP.L z J → Good I.t'.PP.L z J' →
        sval (show LB.Sec (LB.LinComb Xo.univ.t.PP.L (K := Fin 1)
            (fun _ => (snd (ptO Xo yI.1.x) Xo.univ.t.G).left) (fun _ => (k : ℤ))) from F) zp z J =
          ((gv I.w1 r z (fun _ => J (r ≫ I.m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval σt r z J') ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (z : Z) (J : (Z ⟶ I.G.G.left) → I.G.PP.L.ι)
      (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good I.G.PP.L z J → Good I.t'.PP.L z J' →
      sval σ (r ≫ I.m2.φ) z J =
        ((gv I.w2 r z (fun _ => J (r ≫ I.m2.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval σt r z J'

def FrameTieSt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] : Prop :=
  ∀ (Tc : CDVR) (io : c.F →+* Tc.Fr) (yI : IntFr Xo c Tc io) (C : IntegralChartA3 Xo c Tc io yI),
    letI := io.toAlgebra
    ∃ x' : ∀ m, jOG (𝟙 (Sp Tc.Fr)) (chD C.ch) m 1 ⟶ C.I.t'.G,
      (∀ m, (x' m).left ≫ C.I.m1.φ = (C.ch.x m).left) ∧
      (∀ m, (x' m).left ≫ C.I.m2.φ =
        spMap (jetCoef (algebraMap Tc.V Tc.Fr) (Fin 1 × Fin (chD C.ch)) m) ≫ (C.xT m).left) ∧
      ∃ eL' : ∀ m, LB.Gen (LB.LinComb C.I.t'.PP.L (K := Fin 1) (fun _ => (x' m).left) (fun _ => (1 : ℤ))),
        ∀ (m : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp Tc.Fr)) (chD C.ch) m 1).left) (z : Z)
          (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (J' : (Z ⟶ C.I.t'.G.left) → C.I.t'.PP.L.ι)
          (J'' : (Z ⟶ C.I.G.G.left) → C.I.G.PP.L.ι),
          Good Xo.univ.t.PP.L z J → Good C.I.t'.PP.L z J' → Good C.I.G.PP.L z J'' →
          val (eL yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP m) r z J =
            gv C.I.w1 (r ≫ (x' m).left) z (fun _ => J ((r ≫ (x' m).left) ≫ C.I.m1.φ))
              (J' ((r ≫ (x' m).left) ≫ 𝟙 _)) * val (eL' m) r z J' ∧
          val (eLG C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.actT C.eT C.wPT m)
              (r ≫ spMap (jetCoef (algebraMap Tc.V Tc.Fr) (Fin 1 × Fin (chD C.ch)) m)) z J'' =
            gv C.I.w2 (r ≫ (x' m).left) z (fun _ => J'' ((r ≫ (x' m).left) ≫ C.I.m2.φ))
              (J' ((r ≫ (x' m).left) ≫ 𝟙 _)) * val (eL' m) r z J'

def zCast {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) : LB.Sec (LPow A L k₂ T) := h ▸ F

theorem natCast_sq (M : ℕ) : ((M : ℤ) ^ 2) = ((M ^ 2 : ℕ) : ℤ) := (Nat.cast_pow M 2).symm

def SplitModel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (I : IntData Xo c Tc io yI.1) : Prop :=
  ∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc.V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc.V))).obj I.G.G)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section



noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory


theorem act_natCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (n : ℕ) : t.act.act (n : 𝓞 E) = 𝟙 _ ^ n := by
  have act0 : t.act.act 0 = 1 := by
    have h0 := t.act.add 0 0
    rw [add_zero] at h0
    exact mul_eq_left.1 h0.symm
  induction n with
  | zero => rw [Nat.cast_zero, act0, pow_zero]
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section



noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def sabMapCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t' : SAB H S'}
    {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : SABMap t' t f' := h ▸ m

theorem sabMapCast_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : (sabMapCast m h).φ = m.φ := by
  subst h
  rfl

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Model

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

theorem key_fwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i) :
    ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i := by
  rw [sec_eq_iff] at h
  rw [scal_eq_iff]
  intro J yy hy
  have hp : bcV ψ x yy ∈ (tB ψ x).PP.L.U (fun _ _ => J 0) := (cpV' ψ x).le J hy
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcV ψ x) yy hp (h _ _ hp)
  have A1 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0))
        ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f (fun _ _ => J 0)) =
      gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U (fun _ => J 0)) (s''.f (fun _ => J 0)) :=
    (gs_secCP (cpU' ψ x) s'' (bcV ψ x) yy _ hp).trans (by rw [bcV_bcU]; rfl)
  have hp2 : (bcV ψ x ≫ pullback.fst _ _) yy ∈
      (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).U (fun _ => J 0) := (cpσ ψ x).le _ hp
  have A2 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0)) ((σB ψ x s0).f (fun _ _ => J 0)) =
      gs (bcPm ψ x) yy ((PPx x).U (fun _ => J 0)) (s0.f (fun _ => J 0)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (bcV ψ x) yy _ hp).trans
      ((gs_secCP (cpθ x) s0 _ yy _ hp2).trans (by rw [Category.assoc, bcV_gxU]; rfl))
  have A3 : bcV ψ x ≫ (tB ψ x).G.hom = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := bcV_snd ψ x
  rw [A1, A2, A3] at h1
  have hJ : (fun _ : Fin 1 => J 0) = J := funext fun k => by rw [Subsingleton.elim k 0]
  rw [hJ] at h1
  have e4 : gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U J) ((secCP (cpS ψ x) s0).f J) =
      gs (bcPm ψ x) yy ((PPx x).U J) (s0.f J) :=
    (gs_secCP (cpS ψ x) s0 (𝟙 _) yy J hy).trans (by rw [Category.id_comp]; rfl)
  exact h1.trans (congrArg _ e4.symm)

theorem key_bwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i) :
    ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i := by
  rw [scal_eq_iff] at h
  rw [sec_eq_iff]
  intro i q hq
  have hq' : bcU ψ x q ∈ (PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit) := (cpU' ψ x).le i hq
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcU ψ x) q hq' (h _ _ hq')
  rw [bcU_fst] at h1
  have B0 : gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i) =
      gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        (s''.f (fun _ => i PUnit.unit PUnit.unit)) :=
    (gs_secCP (cpU' ψ x) s'' (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  have B1 : gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        ((secCP (cpS ψ x) s0).f (fun _ => i PUnit.unit PUnit.unit)) =
      gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((σB ψ x s0).f i) := by
    refine (gs_secCP (cpS ψ x) s0 (bcU ψ x) q _ hq').trans ?_
    rw [bcU_bcPm]
    exact ((gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) q i hq).trans
      ((gs_secCP (cpθ x) s0 _ q _ ((cpσ ψ x).le i hq)).trans (by rfl))).symm
  exact B0.trans (h1.trans (congrArg _ B1))

theorem genBC_frame (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    {K : Type} [Field K] (ρ : S →+* K) (s0 : LB.Sec (PPx x))
    (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i) (s'' : LB.Sec (PPx (spMap ρ ≫ x))) :
    ∃! a : K, ∀ i, s''.f i = scal (spMap ρ ≫ x) a i * (secCP (cpS ρ x) s0).f i := by
  obtain ⟨a, ha, hu⟩ := gen_baseChange hS hT Xo.univ (mA x) (θA x s0) (hθ_of x s0 hgen) ρ (mB ρ x)
    (w := idIso ((tA x).PP.L.pull (mB ρ x).φ)) (σB ρ x s0) (hσ_of ρ x s0) (secCP (cpU' ρ x) s'')
  exact ⟨a, key_fwd ρ x s0 s'' a ha, fun a' ha' => hu a' (key_bwd ρ x s0 s'' a' ha')⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def vspActL {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) :
    ReciprocityTheory.ChartRestriction.G.I2.Vsp dim →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp dim where
  toFun := ReciprocityTheory.ChartRestriction.G.I2.act α
  map_add' v w := by
    ext i
    simp [ReciprocityTheory.ChartRestriction.G.I2.act, mul_add]
  map_smul' c v := by
    ext i
    simp [ReciprocityTheory.ChartRestriction.G.I2.act]
    ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
