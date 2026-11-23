module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Formalism.LocalToGlobal.CharacterGerms.Bundle021
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockOfNormalForm
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle021
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SumEqOfIsHomogeneous
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
public import Formalism.LocalToGlobal.CharacterGerms.Bundle027
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteTorsOfFiniteTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGeneratorOfRosatiAdjointLambdaBundle
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.cartHyp_of_integralGaugedFormalGroupLaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → (∀ g, HasTeich X V g) → ∀ g, X.CartHyp V g := by
  first | exact @GlobalTheory.RowLaw.cartHyp_of_rlaw | exact GlobalTheory.RowLaw.cartHyp_of_rlaw | (intros; apply GlobalTheory.RowLaw.cartHyp_of_rlaw <;> assumption)
end

section

noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.MinorShiftJet

variable {K : Type} [Field K] {V : VF K} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem big_shift (X : RowData K V d I J) (h : X.Alt) {g : Fin 2} {a : ZMod d} (ha : X.big g a) {i : ℕ}
    (hi : Odd i) : X.big (1 - g) (a + (i : ZMod d)) := by
  have hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    rw [ZMod.val_add, ZMod.val_natCast]
    obtain ⟨r, hr⟩ := h.1
    have h2 : 2 ∣ d := ⟨r, by omega⟩
    rw [Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2, Nat.add_mod, Nat.mod_mod_of_dvd _ h2,
      Nat.odd_iff.1 hi]
    omega
  rw [X.big_compl]
  have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
  fin_cases g
  · simp only [Fin.zero_eta] at ha ⊢
    rw [h.2] at ha ⊢
    rw [hpar]; exact fun h' => h' ha
  · simp only [Fin.mk_one] at ha ⊢
    rw [h1, h.2] at ha ⊢
    rw [hpar]; exact fun h' => h' ha

omit [∀ g, Fintype (I g)] in
theorem rename_minor {n N : ℕ} (hN : n ≤ N) (g : Fin 2) (en : Fin N → I g) :
    MvPolynomial.rename (fun x : Fin n × Fin N => (x.1, (⟨g, en x.2⟩ : WV I))) (minorK K n N n) =
      letterDet K g fun c => en (Fin.castLE hN c) := by
  rw [minorK, dite_eq_left ⟨le_rfl, hN⟩, AlgHom.map_det, letterDet]
  congr 1
  refine Matrix.ext fun b c => ?_
  simp

theorem satIn_single (X : RowData K V d I J) (g : Fin 2) (a : ZMod d) {N : ℕ} (p : Fin N → I g)
    (hp : Function.Injective p) (hty : ∀ c, (X.G g).ty (Sum.inl (p c)) = a) :
    X.SatIn g a fun b x => if x = p b then 1 else 0 := by
  have h01 : ∀ (P : Prop) [Decidable P], V.Ge 0 (if P then (1 : K) else 0) := by
    intro P _; split_ifs
    exacts [VF.Ge.one, VF.Ge.zero _]
  refine ⟨⟨fun c x => h01 _, fun x c => if x = p c then 1 else 0, fun x c => h01 _, fun c c' => ?_⟩,
    fun c x hx => if_neg fun h => hx (by rw [h, hty])⟩
  simp [hp.eq_iff, eq_comm]

theorem cc_mvExp' {σ : Type} (x : MvPowerSeries σ K) : constantCoeff (mvExp x) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  change ∑ j ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), coeff 0 (x ^ j) / (j.factorial : K) = 1
  simp

theorem jetAt0_one' {σ : Type} (G : MvPowerSeries σ K) : jetAt0 1 G = constantCoeff G := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', jetAt0_monomial]
  simp [mfact]

theorem mono_resι_var {l i n0 n : ℕ} (hl : 5 ≤ l) (hn : n0 ≤ n) : S0 l i n0 ≤ S0 l i n := by
  unfold S0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.logb l ((n0 : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith [Nat.cast_nonneg (α := ℝ) n0])
  have h1 : Real.logb l ((n0 : ℝ) + 1) ≤ Real.logb l ((n : ℝ) + 1) :=
    Real.logb_le_logb_of_le hl1 (by positivity) (by linarith)
  refine Nat.ceil_mono ?_
  gcongr

theorem sum_positive_of_five_le {l i n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) : 0 < S0 l i n := by
  unfold S0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.logb l ((n : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith)
  refine Nat.ceil_pos.2 ?_
  positivity

theorem window_letterDet (X : RowData K V d I J) (hA : X.Alt) (hl : 5 ≤ V.l) (hn1 : 1 ≤ X.n)
    (g : Fin 2) (a : ZMod d) (ha : X.big g a) (i : ℕ) (hi : Odd i) (hid : i < d)
    (p : Fin X.n → I g) (p' : Fin X.n → I (1 - g)) (hp : Function.Injective p) (hp' : Function.Injective p')
    (hty : ∀ c, (X.G g).ty (Sum.inl (p c)) = a)
    (hty' : ∀ c, (X.G (1 - g)).ty (Sum.inl (p' c)) = a + (i : ZMod d)) :
    Windows (S0 V.l i X.n) {y | ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) K),
      (∀ g, (S g).IsT (t g)) ∧ ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
          (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤ ((blockBd V.l X.n X.m i y : ℝ) : WithTop ℝ)} := by
  have := X.charZero
  obtain ⟨n0, e, v', Φ, hM, -⟩ := (GlobalTheory.T.rowData_mainTerm_normalForm_and_levelOne K V d I J X).1 hA hl g a ha i hi hid _ _
    (satIn_single X g a p hp hty) (satIn_single X (1 - g) _ p' hp' hty')
  have hn : n0 ≤ X.n := hM.1.2
  obtain ⟨hR, hH1, hH2, -⟩ := GlobalTheory.T.mainTerm_implies_rowHypothesis K V d I J X g a i _ _ n0 e v' Φ hM hn
  obtain ⟨S, t, hSt, hr, tt, tt', hB, hy⟩ :=
    block_of_normal_form X g a i p p' hp hp' n0 e v' Φ hM hn _ hR
  have hrank : X.n - n0 ≤ (i + 1) * X.m := by
    have h1 := hM.1.1
    have h2 : (i + 1) * X.m = (i + 1) * X.j' + X.j + i * X.j := by unfold RowData.m; ring
    omega
  have hgood : ∀ y : ℕ, V.v (jetAt0 (detL K X.n ^ (V.l ^ i * y) * detR K X.n ^ y)
      (BiF V.l i n0 X.n y hr tt tt')) ≤ (((bdP V.l i X.n X.n y + ((i : ℝ) + 1) * X.m * ((V.l : ℝ) ^ i + 1) * y /
        ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ) ∨ y = 0 →
      ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
          (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤ ((blockBd V.l X.n X.m i y : ℝ) : WithTop ℝ) := by
    intro y h
    obtain ⟨gr, hgr, hv⟩ := hy y
    refine ⟨gr, hgr, hv.trans ?_⟩
    by_cases h0 : y = 0
    · subst h0
      simp only [blockBd, if_true, mul_zero, pow_zero, mul_one, jetAt0_one', BiF, ite_self, one_mul, map_prod,
        cc_mvExp', Finset.prod_const_one, V.v.map_one]
      rfl
    · rw [blockBd, if_neg h0]
      exact h.resolve_right h0
  refine ⟨⟨S, t, hSt, hgood 0 (Or.inr rfl)⟩, fun Y0 => ?_⟩
  rcases Nat.eq_zero_or_pos n0 with h0 | h0
  · subst h0
    refine ⟨Y0, ⟨S, t, hSt, hgood Y0 (Or.inl ?_)⟩, le_rfl, Nat.lt_add_of_pos_right (sum_positive_of_five_le hl hn1)⟩
    have hl1 : (1 : ℝ) < V.l := by exact_mod_cast (by omega : 1 < V.l)
    rw [GlobalTheory.T.blockValue_on_rows_eq K V.l i 0 X.n hn hr tt tt' _ hB Y0]
    refine (GlobalTheory.OddBlock.content_and_window.1 K V.v V.l V.l_prime hl V.v_l i X.n 0 Y0 hi hn1 hn _ ?_).trans ?_
    · have : LamP K V.l i 0 (X.restrictedCurveSystemSeries g a i hn e v') Y0 = 1 := by
        simp [LamP, detL, detR, jetAt0_one', cc_mvExp']
      rw [this, V.v.map_one]
      have hn' : (1 : ℝ) ≤ X.n := by exact_mod_cast hn1
      have h0 : 0 ≤ Real.logb V.l (X.n : ℝ) := Real.logb_nonneg hl1 hn'
      have : 0 ≤ bdP V.l i 0 X.n Y0 := by
        simp only [bdP, Nat.cast_zero, zero_mul, zero_add]; positivity
      exact_mod_cast this
    · rw [WithTop.coe_le_coe]
      have h3 : ((X.n : ℝ) - ((0 : ℕ) : ℝ)) ≤ ((i : ℝ) + 1) * X.m := by
        rw [Nat.cast_zero, sub_zero]; exact_mod_cast hrank
      have : (0 : ℝ) < (V.l : ℝ) - 1 := by linarith
      gcongr
  · obtain ⟨y, h1, h2, h3⟩ := GlobalTheory.OddBlock.content_and_window.2 K V.v V.l V.l_prime hl V.v_l i hi n0 X.n X.m hn h0 hrank hr tt tt' _
      hB hH1 hH2 Y0
    exact ⟨y, ⟨S, t, hSt, hgood y (Or.inl h3)⟩, h1, h2.trans_le (Nat.add_le_add_left (mono_resι_var hl hn) _)⟩

end GlobalTheory.MinorShiftJet

namespace GlobalTheory

open MinorShiftJet

theorem oddBlock_supply : BiSupply ∧ RF.BiSupply := by
  constructor
  · intro K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid
    have h1 : X.n ≤ X.rk g a := (Nat.le_add_right _ _).trans (X.rk_big g a ha).ge
    have h2 : X.n ≤ X.rk (1 - g) (a + (i : ZMod d)) :=
      (Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge
    have key := window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c))
      (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c))
      ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2))
      (fun c => F.en_ty _ _ _) (fun c => F.en_ty _ _ _)
    rw [← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))] at key
    exact key
  · intro K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid
    have h1 : X.n ≤ X.rkF g a := (Nat.le_add_right _ _).trans (X.rk_big g a ha).ge
    have h2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) :=
      (Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge
    have key := window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c))
      (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c))
      ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2))
      (fun c => F.en_ty _ _ _) (fun c => F.en_ty _ _ _)
    rw [← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))] at key
    exact key

end GlobalTheory
end
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory

theorem nuLocC_le_nuPlE_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.DescentSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ T io y C3 C _ _ V ι hι k Y hY a n
  obtain ⟨hint, hval⟩ := GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι
  unfold FBChart.nuPlE
  refine le_iInf₂ ?_
  rintro x ⟨P, hP, f, hf, rfl⟩
  have hh : MvPowerSeries.constantCoeff (a3h C3) = 0 := by
    let _ := io.toAlgebra
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ C3.ch.gauge.ax0 0 fun _ => rfl
  unfold FBChart.nab
  rw [hY.h, hY.w0, hY.k]
  refine GlobalTheory.nabValN_lower_bound_baseChange T C V.v ι V.RR (fun x => Iff.rfl) hint _ (𝓞 E) (a3B C3) Y.B hY.F hY.act (a3h C3) hh H.w0 k (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) (nuLocC C3 (eOf T V) k a n) ?_ P hP f hf
  intro Q hQ g hg
  rw [← hval]
  unfold nuLocC
  exact iInf_le_of_le Q (iInf_le_of_le hQ (iInf_le_of_le g (iInf_le_of_le hg le_rfl)))

end GlobalTheory
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlphaPair

section Eval

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def evP {n d : ℕ} (v : Fin n → Fin d → A) (f : PS R n d) : A := nEval f (fun q : Fin n × Fin d => v q.1 q.2)

def addP {d : ℕ} (F : Fin d → PS R 2 d) (a b : Fin d → A) : Fin d → A := fun j => evP ![a, b] (F j)

def cv {d : ℕ} (ga : Fin d → PowerSeries R) (t : A) : Fin d → A :=
  fun j => nEval (σ := Unit) (ga j) (fun _ => t)

variable {κ : Type} [Fintype κ] [DecidableEq κ] {a : κ → A} (ha : ∀ i, IsNilpotent (a i))

def evHom : MvPowerSeries κ R →+* A :=
  (MvPowerSeries.constantCoeff : MvPowerSeries Empty A →+* A).comp
    (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C a ha)).toRingHom

theorem evHom_apply (f : MvPowerSeries κ R) : evHom ha f = nEval f a := by
  simp [evHom, MvPowerSeries.coe_substAlgHom, ChartCompare.subst_C_eq f a ha]

include ha

theorem nEval_add (f g : MvPowerSeries κ R) : nEval (f + g) a = nEval f a + nEval g a := by
  simp only [← evHom_apply ha, map_add (f := _)]

theorem nEval_sub (f g : MvPowerSeries κ R) : nEval (f - g) a = nEval f a - nEval g a := by
  simp only [← evHom_apply ha, map_sub]

theorem nEval_one : nEval (1 : MvPowerSeries κ R) a = 1 := by simp only [← evHom_apply ha, map_one]

end Eval

section Points

variable {S S' : Scheme.{0}} {Ω : Type} [Field Ω]

abbrev Fam (s : Sp Ω ⟶ S) (G : Over S) : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], A → (overAt s A ⟶ G)

def IsAlpha (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G) : Prop :=
  (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 →
    g B (f a) = homAt s f ≫ g A a) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → g A (a + a') = g A a * g A a'

def Orth (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (g : Fam s G) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ e : A, e ^ 2 = 0 →
    ∀ z : overAt s A ⟶ G, homAt s π ≫ z = 1 → z ^ p = 1 → CubWeil c p (g A e) z 1

def NonDeg (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) : Prop :=
  ∀ g : Fam s G, IsAlpha p s G g → Orth p s G c g → g (DualNumber Ω) DualNumber.eps = 1

def Perf (n : ℕ) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G), x ^ n = 1 →
    (∀ (T' : Over S) (ρ : T' ⟶ T) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1) → x = 1

abbrev PtHom (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S') (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (overAt s A ⟶ G) →* (overAt s' A ⟶ B)

abbrev TorHom (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (Multiplicative X →* Aˣ) →* (overAt s A ⟶ G)

def IsTorExt (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S') (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (X : Type)
    [AddCommGroup X] (τ : PtHom s s' G B) (io : TorHom s G X) : Prop :=
  (∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A') (x : overAt s A ⟶ G),
    τ A' (homAt s f ≫ x) = homAt s' f ≫ τ A x) ∧
  (∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A')
    (χ : Multiplicative X →* Aˣ), io A' ((Units.map (f : A →* A')).comp χ) = homAt s f ≫ io A χ) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A], Function.Injective (io A)) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt s A ⟶ G), τ A x = 1 ↔ ∃ χ, io A χ = x) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
    ∀ y : overAt s' A ⟶ B, homAt s' π ≫ y = 1 → ∃ x : overAt s A ⟶ G, homAt s π ≫ x = 1 ∧ τ A x = y

def Transfer (n : ℕ) {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'} {G : Over S} [GrpObj G] [IsCommMonObj G] {B : Over S'} [GrpObj B]
    [IsCommMonObj B] {L : RigLB G} (c : CubicalStr G L) {M : RigLB B} (c' : CubicalStr B M) (τ : PtHom s s' G B) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (x y : overAt s A ⟶ G), CubWeil c n x y 1 → CubWeil c' n (τ A x) (τ A y) 1

abbrev PtFam (s : Sp Ω ⟶ S) (G : Over S) (d : ℕ) : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (Fin d → A) → (overAt s A ⟶ G)

def IsJetPt {V : Type} [CommRing V] (β : V →+* Ω) {G : Over (Sp V)} {d : ℕ}
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (P : PtFam (spMap β) G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (m : ℕ) (ψ : Jet V (Fin 1 × Fin d) m →+* A),
    (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) →
    (P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))).left = spMap ψ ≫ (x m).left

def IsPtLaw (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] {d : ℕ} (F : Fin d → PS Ω 2 d) (P : PtFam s G d) : Prop :=
  (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : Fin d → A),
    (∀ j, IsNilpotent (a j)) → P B (fun j => f (a j)) = homAt s f ≫ P A a) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A], P A 0 = 1) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (a b : Fin d → A), (∀ j, IsNilpotent (a j)) → (∀ j, IsNilpotent (b j)) →
    P A (addP F a b) = P A a * P A b

def IsPtUniv (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] {d : ℕ} (P : PtFam s G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
    (∀ a : Fin d → A, (∀ j, IsNilpotent (a j)) → P A a = 1 → a = 0) ∧
    ∀ z : overAt s A ⟶ G, homAt s π ≫ z = 1 → ∃ a : Fin d → A, (∀ j, IsNilpotent (a j)) ∧ P A a = z

def IsPtCube (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) {d : ℕ}
    (F : Fin d → PS Ω 2 d) (ph1 ph2 : PS Ω 3 d) (P : PtFam s G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (I : Ideal A), IsNilpotent I →
    ∀ (z : (overAt s A).left) (J), Good L.L z J →
    ∃ e : (Fin d → A) → (Fin d → A) → ((overAt s A).left.presheaf.stalk z)ˣ,
      ∀ a b u : Fin d → A, (∀ j, a j ∈ I) → (∀ j, b j ∈ I) → (∀ j, u j ∈ I) →
        (cubV c z J (P A a) (P A b) (P A u) * e a u * e b u).val =
          gs (𝟙 (overAt s A).left) z ⊤ (toΓ A (evP ![a, b, u] ph1)) * (e (addP F a b) u).val ∧
        (cubV c z J (P A b) (P A u) (P A a) * e a b * e a u).val =
          gs (𝟙 (overAt s A).left) z ⊤ (toΓ A (evP ![a, b, u] ph2)) * (e a (addP F b u)).val

section Basic

variable {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'} {G : Over S} [GrpObj G] {p : ℕ}

theorem hom_comp {A B C : Type} [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] [CommRing C] [Algebra Ω C]
    (f : A →ₐ[Ω] B) (g : B →ₐ[Ω] C) : homAt s g ≫ homAt s f = homAt s (g.comp f) :=
  Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp s f g

theorem hom_id {A : Type} [CommRing A] [Algebra Ω A] : homAt s (AlgHom.id Ω A) = 𝟙 _ :=
  Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_id s

theorem IsAlpha.zero {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) (A : Type) [CommRing A] [Algebra Ω A] :
    g A 0 = 1 := by
  have := h.2 A 0 0 (zero_pow hp) (zero_pow hp)
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem IsAlpha.nsmul {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) {A : Type} [CommRing A] [Algebra Ω A] {a : A}
    (ha : a ^ p = 0) (n : ℕ) : g A (n * a) = g A a ^ n := by
  induction n with
  | zero => simpa using h.zero hp A
  | succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, h.2 A _ _ (by rw [mul_pow, ha, mul_zero]) ha, ih, pow_succ]

theorem IsAlpha.pow_eq_one [CharP Ω p] {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) {A : Type} [CommRing A]
    [Algebra Ω A] {a : A} (ha : a ^ p = 0) : g A a ^ p = 1 := by
  rw [← h.nsmul hp ha, ← map_natCast (algebraMap Ω A), CharP.cast_eq_zero, map_zero, zero_mul, h.zero hp]

theorem IsAlpha.map {B : Over S'} [GrpObj B] {X : Type} [AddCommGroup X] {τ : PtHom s s' G B} {io : TorHom s G X}
    (hτ : IsTorExt s s' G B X τ io) {g : Fam s G} (h : IsAlpha p s G g) :
    IsAlpha p s' B (fun A _ _ a => τ A (g A a)) :=
  ⟨fun A A' _ _ _ _ f a ha => by beta_reduce; rw [h.1 A A' f a ha, hτ.1],
    fun A _ _ a a' ha ha' => by beta_reduce; rw [h.2 A a a' ha ha', map_mul]⟩

theorem cubWeil_of_injective [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {n : ℕ} {A B : Type} [CommRing A]
    [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (hf : Function.Injective f) {x y : overAt s A ⟶ G}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (h : CubWeil c n (homAt s f ≫ x) (homAt s f ≫ y) 1) : CubWeil c n x y 1 := by
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c hx hy
  have e := congrArg Units.val ((hζ.comp (homAt s f)).unique h)
  have inj : Function.Injective (homAt s f).left.appTop.hom := by
    have h₁ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* B))
    have h₂ : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom (f : A →+* B)).hom :=
      hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
    rw [← h₁] at h₂
    exact Function.Injective.of_comp (f := (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom) h₂
  obtain rfl : ζ = 1 := Units.ext (inj (e.trans (map_one _).symm))
  exact hζ

theorem cubWeil_mul_right [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {n : ℕ} {T : Over S} {x y y' : T ⟶ G}
    (h : CubWeil c n x y 1) (h' : CubWeil c n x y' 1) : CubWeil c n x (y * y') 1 := by
  simpa using (h.symm.mul_left h'.symm).symm

end Basic

end Points

section Series

def c2 {R : Type} [CommRing R] {d : ℕ} (ph2 : PS R 3 d) (u : Fin d → R) : PS R 2 d :=
  fun mu => ∑ i, u i * MvPowerSeries.coeff
    (mu.mapDomain (fun q : Fin 2 × Fin d => (q.1.succ, q.2)) + Finsupp.single ((0 : Fin 3), i) 1) ph2

def AddMod (p : ℕ) {Ω : Type} [Field Ω] {d : ℕ} (F : Fin d → PS Ω 2 d) (ga : Fin d → PowerSeries Ω) : Prop :=
  ∀ i (mu : Fin 2 →₀ ℕ), mu 0 < p → mu 1 < p → MvPowerSeries.coeff mu
    (MvPowerSeries.subst (fun q : Fin 2 × Fin d => Formalism.L2.FormalSeriesBounds.cvAt (MvPowerSeries.X q.1) (ga q.2)) (F i) -
      Formalism.L2.FormalSeriesBounds.cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (ga i)) = 0

def Degenerate (p : ℕ) {Ω : Type} [Field Ω] {d : ℕ} (F : Fin d → PS Ω 2 d) (ph2 : PS Ω 3 d) : Prop :=
  ∃ ga : Fin d → PowerSeries Ω, (∀ i, PowerSeries.constantCoeff (ga i) = 0) ∧ (∃ i, PowerSeries.coeff 1 (ga i) ≠ 0) ∧
    AddMod p F ga ∧ ∃ b : PS Ω 1 d, c2 ph2 (fun i => PowerSeries.coeff 1 (ga i)) =
      ev (n := 2) ![addOf F (pt Ω d 0) (pt Ω d 1)] b - ev (n := 2) ![pt Ω d 0] b - ev (n := 2) ![pt Ω d 1] b

end Series

end GlobalTheory.AlphaPair
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generator_of_rosatiAdjoint_lambdaBundle : ∀ (O : Type) [CommRing O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)) (Z : Scheme.{0}) (Q : LB Z) (ψ₂ : (P.A ⊗ P.A).left ⟶ Z), Q.IsLB → Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) → ∀ f f' : P.A ⟶ P.A, IsMonHom f → IsMonHom f' → Out.RosatiAdj P.A P.L f f' → ∃ t : LB.Gen (LB.LinComb Q (K := Fin 2) ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]), t.IsGen := by
  first | exact @GlobalTheory.RosGen.exists_gen_of_rosatiAdj | exact GlobalTheory.RosGen.exists_gen_of_rosatiAdj | (intros; apply GlobalTheory.RosGen.exists_gen_of_rosatiAdj <;> assumption)
end
