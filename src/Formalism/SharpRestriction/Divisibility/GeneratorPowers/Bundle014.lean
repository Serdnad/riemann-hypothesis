module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle009
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

namespace GaugeR

variable {R ι : Type} [CommRing R]

theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (a : R) : monomial e a ∈ orig R ι ^ e.degree := by
  rw [monomial_eq]
  apply Ideal.mul_mem_left
  unfold Finsupp.prod
  have hpow : orig R ι ^ e.degree = ∏ i ∈ e.support, orig R ι ^ e i := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hpow]
  exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (show (X i : MvPolynomial ι R) ∈ orig R ι from Ideal.subset_span (Set.mem_range_self i)) _)

theorem mem_orig_pow_of_coeff (n : ℕ) (p : MvPolynomial ι R) (h : ∀ e, e.degree < n → AddMonoidAlgebra.coeff p e = 0) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ (fun e he => ?_)
  have hn : n ≤ e.degree := by
    by_contra hlt
    push_neg at hlt
    exact (mem_support_iff.mp he) (h e hlt)
  exact Ideal.pow_le_pow_right hn (monomial_mem_orig_pow e _)

variable [Fintype ι] [DecidableEq ι]

theorem psJet_eq_mk (m : ℕ) (f : MvPowerSeries ι R) (p : MvPolynomial ι R)
    (h : ∀ e, e.degree ≤ m → AddMonoidAlgebra.coeff p e = MvPowerSeries.coeff e f) :
    psJet m f = Ideal.Quotient.mk _ p := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of_coeff
  intro e he
  rw [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc m f e (by omega), h e (by omega), sub_self]

theorem psJet_mul (m : ℕ) (f g : MvPowerSeries ι R) : psJet m (f * g) = psJet m f * psJet m g := by
  have key : psJet m (f * g) = Ideal.Quotient.mk _ (psTrunc m f * psTrunc m g) := by
    refine psJet_eq_mk m _ _ (fun e he => ?_)
    rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hd : x.1.degree + x.2.degree ≤ m := by
      rw [← map_add Finsupp.degree, hx']
      exact he
    rw [GermFun.coeff_psTrunc m f x.1 (by omega), GermFun.coeff_psTrunc m g x.2 (by omega)]
  rw [key, map_mul]
  rfl

theorem psJet_one (m : ℕ) : psJet m (1 : MvPowerSeries ι R) = 1 := by
  rw [psJet_eq_mk m 1 1 (fun e _ => by rw [MvPolynomial.coeff_one, MvPowerSeries.coeff_one]; exact if_congr eq_comm rfl rfl), map_one]

theorem psJet_pow (m : ℕ) (f : MvPowerSeries ι R) (k : ℕ) : psJet m (f ^ k) = psJet m f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, psJet_one]
  | succ k ih => rw [pow_succ, pow_succ, psJet_mul, ih]

theorem aeval_scale_monomial (s : ι → R) (e : ι →₀ ℕ) (a : R) :
    aeval (fun i => C (s i) * X i) (monomial e a : MvPolynomial ι R) =
      monomial e (a * e.prod fun i k => s i ^ k) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
  rw [map_mul, map_finsuppProd, MvPolynomial.algebraMap_eq]
  ring

theorem coeff_aeval_scale (s : ι → R) (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun i => C (s i) * X i) p) e = (e.prod fun i k => s i ^ k) * AddMonoidAlgebra.coeff p e := by
  induction p using MvPolynomial.induction_on' with
  | monomial e' a =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem jetMap_mk {ι' : Type} (m : ℕ) (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι')
    (p : MvPolynomial ι R) :
    jetMap φ hφ (Ideal.Quotient.mk (orig R ι ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetSubstP_scale (m : ℕ) (s : ι → R) (f : MvPowerSeries ι R) :
    Formalism.L2.Pj.jetSubstP m (fun i => C (s i) * X i) (psJet m f) =
      psJet m (MvPowerSeries.rescale s f) := by
  unfold jetSubstP psJet
  rw [jetMap_mk]
  simp only [map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_zero, sub_zero]
  symm
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  rw [coeff_aeval_scale, GermFun.coeff_psTrunc m f e he, MvPowerSeries.coeff_rescale]

theorem jetAug_psJet (m : ℕ) (f : MvPowerSeries ι R) :
    jetAug (psJet m f) = MvPowerSeries.constantCoeff f := by
  show (MvPolynomial.aeval fun _ => (0 : R)) (psTrunc m f) = _
  rw [MvPolynomial.aeval_zero', Algebra.algebraMap_self_apply]
  show AddMonoidAlgebra.coeff (psTrunc m f) 0 = _
  rw [GermFun.coeff_psTrunc m f 0 (by simp)]
  rfl

theorem exists_ps_of_compat (ρ : ∀ m, Jet R ι m) (h : ∀ m, jetTrunc (ρ (m + 1)) = ρ m) :
    ∃ r : MvPowerSeries ι R, ∀ m, psJet m r = ρ m := by
  classical
  choose P hP using fun m => Ideal.Quotient.mk_surjective (ρ m)
  have hstep : ∀ m, P (m + 1) - P m ∈ orig R ι ^ (m + 1) := by
    intro m
    rw [← Ideal.Quotient.eq]
    have h1 := h m
    rw [← hP (m + 1), ← hP m] at h1
    exact h1
  have hcoef : ∀ n k (e : ι →₀ ℕ), e.degree ≤ n → AddMonoidAlgebra.coeff (P (n + k)) e = AddMonoidAlgebra.coeff (P n) e := by
    intro n k e he
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← ih, ← sub_eq_zero, ← MvPolynomial.coeff_sub]
      exact GermFun.coeff_eq_zero_of_mem (hstep (n + k)) (by omega)
  refine ⟨fun e => AddMonoidAlgebra.coeff (P e.degree) e, fun m => ?_⟩
  rw [← hP m]
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  have h2 := hcoef e.degree (m - e.degree) e le_rfl
  rw [show e.degree + (m - e.degree) = m by omega] at h2
  rw [h2]
  rfl

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem val_rigPow {Z : Scheme.{0}} (k : ℤ) (r : Z ⟶ (𝟙_ (Over Xo.X)).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) :
    val (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig k) r z J = val Xo.univ.t.PP.rig r z J ^ k := by
  unfold rigPow val
  exact map_zpow _ _ _

theorem eSec_act (c : 𝓞 E) : eSec Xo.univ.t.G ≫ (Xo.univ.t.act.act c).left = eSec Xo.univ.t.G := by
  haveI := Xo.univ.t.act.2 c
  unfold eSec
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem eSec_toUnit : eSec Xo.univ.t.G ≫ (toUnit Xo.univ.t.G).left = 𝟙 _ := by
  unfold eSec
  rw [← Over.comp_left]
  simp

theorem exists_beta (wP : PrimTy H Xo) (hwP : IsPrim wP) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : ExpGC.AdTy Xo a) (hwa : wLa.IsGen) (wLb : ExpGC.AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
        (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
          (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
            val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by
  have hL := Xo.univ.t.PP.isLB
  have hrig := Xo.univ.t.PP.rigGen
  obtain ⟨β0, hβ0, hv0⟩ := ExpGC.exists_betaRaw wP hwP.1 a hbb wLa hwa wLb hwb
  have hg := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ β0 hβ0 (eSec Xo.univ.t.G))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hrig
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hrig hrig))
  obtain ⟨g0, hg0, hv1⟩ := exists_gen hL (φ' := (PEmpty.elim : PEmpty.{1} → ((𝟙_ (Over Xo.X)).left ⟶ Xo.univ.t.G.left)))
    (ε' := PEmpty.elim) (by
      intro U _ hU
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, betaφ, betaε,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, eSec_act, Category.comp_id, Finset.univ_unique, Finset.prod_singleton,
        Finset.univ_eq_empty, Finset.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      abel) _ hg
  have hB := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hβ0
    (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen Xo.univ.t.PP.L _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ g0 hg0 (toUnit Xo.univ.t.G).left))
  obtain ⟨β, hβ, hv2⟩ := exists_gen hL (φ' := betaφ (Xo := Xo) a) (ε' := betaε) (by
      intro U _ hU
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_eq_empty, Finset.prod_empty,
        _root_.mul_one]) _ hB
  have hval : ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
      Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
        (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
          val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by
    intro Z r z J hJ
    rw [hv2 Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hv1 Z _ z J hJ, val_mul hJ, val_pull hJ, val_mul hJ,
      val_mul hJ, hv0 Z r z J hJ, hv0 Z _ z J hJ, ← Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  refine ⟨β, hβ, corr_of_val hL fun z J hJ => ?_, hval⟩
  rw [val_pull hJ, hval _ _ z J hJ, val_rigPow]
  simp only [Category.id_comp]
  rw [← Category.assoc (eSec Xo.univ.t.G), eSec_toUnit, Category.id_comp]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def ExpUniqTanSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (x x' : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G),
    IsExpChart y x → IsExpChart y x' → x = x'

def KillAddValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n : ℕ)
    (g : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
    MvPowerSeries.constantCoeff q = 0 → (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) →
    (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
        Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, expVal (g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b)

def ChartIndepTruncSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C C' : ChartAt Xo c y), FrTruncC y C → FrTruncC y C' → ∀ (k n : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S),
    (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) →
    (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      chartVal C k f P = chartVal C' k f' P

theorem chartIndepTrunc_of (hE : ExpChartOfSt) (hG : ExpGaugeOfSt) (hT : TieSt) (hU : ExpUniqTanSt)
    (hGU : GaugeUniqSt) (hK : KillAddValSt) : ChartIndepTruncSt := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C C' hC hC' k n F f f' hf hf' a P hP

  have key : ∀ (x x' : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G), x' = x → IsExpChart y x →
      ∀ (e : ∀ m, ExpFr y x m) (e' : ∀ m, ExpFr y x' m), IsExpGauge y x e → IsExpGauge y x' e' →
      ∀ (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
      (∀ b, IsExpGerm y x e k (F b) (g b)) → (∀ b, IsExpGerm y x' e' k (F b) (g' b)) →
      (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b)) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) := by
    intro x x' hxx hx e e' he he' g g' hg hg'
    subst hxx
    obtain ⟨q, hq0, hq2, hqc, hqf⟩ := hGU E H Dw l Xo c S y _ hx e e' he he'
    have hgg : ∀ b, g' b = g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) :=
      fun b => hqf k (F b) (g b) (g' b) (hg b) (hg' b)
    simp only [hgg]
    exact (hK E H Dw l c S k n g q hq0 hq2 hqc a P hP).symm
  obtain ⟨φ, hφ, hx⟩ := hE E H Dw l Xo c S y C
  obtain ⟨φ', hφ', hx'⟩ := hE E H Dw l Xo c S y C'
  obtain ⟨e, he, heo⟩ := hG E H Dw l Xo c hstar S y C hC φ hφ hx
  obtain ⟨e', he', heo'⟩ := hG E H Dw l Xo c hstar S y C' hC' φ' hφ' hx'
  choose g hg hgv using fun b => hT E H Dw l Xo c hstar S y C φ hφ e heo k (F b) (f b) (hf b)
  choose g' hg' hgv' using fun b => hT E H Dw l Xo c hstar S y C' φ' hφ' e' heo' k (F b) (f' b) (hf' b)
  have h1 : chartVal C k f P =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) := by
    simp only [chartVal, hgv]
  have h2 : chartVal C' k f' P =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) := by
    simp only [chartVal, hgv']
  rw [h1, h2]
  exact key _ _ (hU E H Dw l Xo c S y _ _ hx' hx) hx e e' he he' g g' hg hg'

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj

namespace CIndFrFix

open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

def lg (G : FGLaw S d) {n : ℕ} (j : Fin n) : Pt S n d := fun i => ev (n := n) ![pt S d j] (logOf G i)

def bilL (G : FGLaw S d) (cc : Fin d → Fin d → S) : PS S 2 d :=
  ∑ i, ∑ l, cc i l • (lg G (0 : Fin 2) i * lg G (1 : Fin 2) l)

def expP {n : ℕ} (f : PS S n d) : PS S n d := PowerSeries.subst f (PowerSeries.exp S)

def diagL {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) : PS S 1 d :=
  ev (n := 1) ![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] (bilL B.G cc)

end CIndFrFix

open CIndFrFix

def FrTruncFixSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧ cc 0 = 0 ∧ (∀ m i j, cc m i j = cc m j i) ∧
      (∀ m (a : 𝓞 E), Matrix.transpose (ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a)) * Matrix.of (cc m) =
        Matrix.of (cc m) * ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act (H.bar a))) ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))

def GermFixSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } →
      (∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))) →
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
        ∃ f' : MvPowerSeries (Fin 1 × Fin C.d) S, IsGerm y C.d C.x C.B.A.act e' C.wP k F f' ∧
          ∀ D, psJet D f' = psJet D (f * expP ((k : S) • diagL C.B H.w0 (cc D)))

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

theorem Q_nonneg (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (χ : D.toPre.X) : 0 ≤ Q χ := by
  by_cases hχ : χ = 0
  · rw [hχ, Q_zero hϖ (D := D) (Q := Q) (hQ := hQ)]
  · exact le_trans zero_le_one (Q_pos hϖ (D := D) (Q := Q) (hQ := hQ) hχ)

end Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt
end
end
