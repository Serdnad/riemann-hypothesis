module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle212
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle018
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.StdNab

open IsDedekindDomain

theorem mem_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x a := by
  refine ⟨fun hx a => GlobalTheory.NabStab.int_of_mem_colLat_one hx a, fun h => ?_⟩
  choose y hy using h
  have hx : x = ∑ j, y j • fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Units.val_one, Matrix.one_apply, Algebra.smul_def, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hy]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem tauLat_stdLat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {Ix : Type} {n : ℕ}
    (emb : Ix → E →+* K) (t : Ix) : tauLat emb t (stdLat E n) = colLat (1 : GL (Fin n) K) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine (mem_colLat_one _).2 fun a => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hx a (Set.mem_univ a))
    refine ⟨⟨emb t (x a), ?_⟩, rfl⟩
    rw [← hy]
    exact map_isIntegral_int (emb t) y.isIntegral_coe
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨fun a => if a = j then 1 else 0, fun a _ => ?_, ?_⟩
    · by_cases h : a = j
      · exact Submodule.mem_one.2 ⟨1, by simp [h]⟩
      · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩
    · funext a
      by_cases h : a = j <;> simp [h, Matrix.one_apply]

theorem dualFr_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} :
    dualFr (colLat (1 : GL (Fin n) K)) = colLat (1 : GL (Fin n) K) := by
  ext φ
  constructor
  · intro h
    refine (mem_colLat_one _).2 fun a => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (h _ (Submodule.subset_span ⟨a, rfl⟩))
    refine ⟨y, ?_⟩
    rw [hy]
    simp [dotProduct, Matrix.one_apply]
  · intro h x hx
    choose y hy using (mem_colLat_one _).1 h
    choose z hz using (mem_colLat_one _).1 hx
    refine Submodule.mem_one.2 ⟨∑ a, y a * z a, ?_⟩

    simp only [map_sum, map_mul, hy, hz, dotProduct]

theorem mem_of_forall_locP {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module (𝓞 K) W]
    (T : Submodule (𝓞 K) W) (x : W) (h : ∀ w : HeightOneSpectrum (𝓞 K), x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) : x ∈ T := by
  by_contra hx
  let I : Ideal (𝓞 K) := T.comap (LinearMap.toSpanSingleton (𝓞 K) W x)
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : 𝓞 K) ∈ I := hI ▸ Submodule.mem_top
    exact hx (by simpa [I] using h1)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩
  exact hs (hIm (show s ∈ I from hsx))

theorem polyAction_one₂ {K Ix : Type} [Field K] [Fintype Ix] {n : ℕ} (lam : Ix → DomWeight n) (F : Pol K Ix n) :
    actP lam 1 F = F := by
  simp [Formalism.L2.DIV.actP, detTwK_one, trAct_one]

theorem nabP_colLat_one {K Ix : Type} [Field K] [NumberField K] [Fintype Ix] {n : ℕ} (lam : Ix → DomWeight n) :
    nabP lam (fun _ => colLat (1 : GL (Fin n) K)) = nabStd K lam := by
  ext F
  constructor
  · intro hF
    refine mem_of_forall_locP _ _ fun w => ?_
    have h := nabP_colLat_le lam 1 w hF
    rwa [inv_one, polyAction_one₂] at h
  · intro hF
    simp only [nabP, transLat, Submodule.mem_iInf]
    intro w B hB
    exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd K Ix n lam w B⁻¹ (fun t => GlobalTheory.NabStab.isBasisAt_inv w (B t) (hB t)) F
      ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

theorem eval_extremal {R : Type} [CommRing R] {n : ℕ} (lam : DomWeight n) :
    eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0) (extremal R n lam) = 1 := by
  unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  have h : ∀ (k : ℕ) (h1 h2 : k ≤ n),
      (eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0)).mapMatrix
        (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [Matrix.one_apply, Fin.ext_iff]
  rw [h, Matrix.det_one, one_pow]

theorem nabAtr_stdLat : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (Ix : Type) [Fintype Ix] (n : ℕ) (emb : Ix → E →+* K) (lam : Ix → DomWeight n), (∀ F : VV K lam, F ∈ nabAtr emb lam (stdLat E n) ↔ (F : Pol K Ix n) ∈ nabStd K lam) ∧ (ten fun t => extremal K n (lam t)) ∈ nabStd K lam ∧ ∀ x : K, x • (ten fun t => extremal K n (lam t)) ∈ nabStd K lam → ∃ o : 𝓞 K, x = (o : K) := by
  intro E K _ _ _ _ Ix _ n emb lam
  refine ⟨fun F => ?_, ?_, fun x hx => ?_⟩
  · unfold nabAtr nabK
    simp only [tauLat_stdLat, dualFr_colLat_one, nabP_colLat_one]
    rfl
  · refine Submodule.subset_span ⟨fun t => extremal K n (lam t), fun t => ?_, rfl⟩
    exact ⟨extremal (𝓞 K) n (lam t), Formalism.GradedWeylDivisibility.hwMem (𝓞 K) n n le_rfl _ (natW_antitone (lam t)),
      map_extremal _ n (lam t)⟩
  · obtain ⟨Q, hQ⟩ := GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hx
    let e : ∀ (R : Type) [CommRing R], Ix × Fin n × Fin n → R := fun R _ v => if v.2.1 = v.2.2 then 1 else 0
    refine ⟨eval (e (𝓞 K)) Q, ?_⟩
    have h1 : eval (e K) (ten fun t => extremal K n (lam t)) = 1 := by
      unfold ten
      rw [map_prod]
      refine Finset.prod_eq_one fun t _ => ?_
      unfold Formalism.GradedWeylDivisibility.blockEmb
      rw [eval_rename]
      exact eval_extremal (lam t)
    have h2 : eval (e K) (map (algebraMap (𝓞 K) K) Q) = algebraMap (𝓞 K) K (eval (e (𝓞 K)) Q) := by
      have h3 : e K = algebraMap (𝓞 K) K ∘ e (𝓞 K) := by
        funext v
        by_cases h : v.2.1 = v.2.2 <;> simp [e, h]
      rw [h3, ← map_eval]
    have h4 := congrArg (eval (e K)) hQ
    rw [GlobalTheory.NabStab.toK_apply, h2, smul_eval, h1, mul_one] at h4
    exact h4.symm

end GlobalTheory.StdNab
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.NabLinear

section Formal

variable {k : Type} [CommRing k] {d : ℕ}

theorem dof_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (c : k) (f : PS k 1 d) :
    Germ.Dof F u (MvPowerSeries.C c * f) = MvPowerSeries.C c * Germ.Dof F u f := by
  unfold Germ.Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← MvPowerSeries.smul_eq_C_mul, Derivation.map_smul, MvPowerSeries.smul_eq_C_mul]
  ring

theorem dof_iter_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (c : k) (n : ℕ) (f : PS k 1 d) :
    (Germ.Dof F u)^[n] (MvPowerSeries.C c * f) = MvPowerSeries.C c * (Germ.Dof F u)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dof_C_mul, ih]

theorem dmon_C_mul (F : Fin d → PS k 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → k) (m : κ →₀ ℕ) (c : k)
    (f : PS k 1 d) :
    Germ.DmonOf F u m (MvPowerSeries.C c * f) = MvPowerSeries.C c * Germ.DmonOf F u m f := by
  unfold Germ.DmonOf
  induction (Finset.univ : Finset κ).toList with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, dof_iter_C_mul]

theorem nabVal_C_mul [Algebra ℚ k] {R : Type} [CommRing R] [Algebra R k] {O : Type} [CommRing O] [StarRing O]
    (B : Germ.FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (c : k) (f : PS k 1 d) {κ : Type} [Fintype κ]
    (u : κ → Fin d → k) (P : MvPolynomial κ k) :
    B.nabVal k h w0 q (MvPowerSeries.C c * f) u P = c * B.nabVal k h w0 q f u P := by
  unfold Germ.FB.nabVal Germ.DpolyOf

  rw [_root_.mul_assoc, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dmon_C_mul]
  simp only [map_mul, MvPowerSeries.constantCoeff_C]
  ring

theorem psJet_C {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (c : k) :
    psJet m (MvPowerSeries.C c : MvPowerSeries κ k) = algebraMap k (Jet k κ m) c := by
  have h : (MvPowerSeries.C c : MvPowerSeries κ k) = ((MvPolynomial.C c : MvPolynomial κ k) : MvPowerSeries κ k) := by
    simp
  rw [h, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
  rfl

end Formal

section Sec

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

omit [GrpObj A] in
theorem gs_liftFun {T : Over S0} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) {Z : Scheme.{0}}
    (q : Z ⟶ (T ⊗ A).left) (z : Z) (hz : q z ∈ W) :
    gs q z W (liftFun A W r) = gs (q ≫ (fst T A).left) z ⊤ r :=
  (gs_res q z le_top hz _).trans (gs_pull q (fst T A).left z ⊤ trivial r)

theorem isValueAt_scale {T T' : Over S0} (g : T' ⟶ T) {F F' : LB.Sec (LPow A L a T)} {r : Γ(T.left, ⊤)}
    (hF : ∀ j, F'.f j = liftFun A _ (T := T) r * F.f j) {F₁ F₂ : LB.Sec (LPow A L a T')}
    (h₁ : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) F F₁)
    (h₂ : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) F' F₂) {z : T' ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T'.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T'.left, ⊤)}
    (hv : IsValueAt A L a F₁ z τ v) : IsValueAt A L a F₂ z τ (g.left.appTop.hom r * v) := by
  intro j
  have key : (T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (F₂.f j)) =
      (T'.left.presheaf.map (homOfLE le_top).op).hom (g.left.appTop.hom r) *
      (T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (F₁.f j)) := by
    apply fn_ext
    intro x hx
    have hP := val_le A L z j hx
    have hP' : (𝟙 T'.left ≫ (ptSecT A z).left) x ∈ (LPow A L a T').U j := hP
    have hQ : ((𝟙 T'.left ≫ (ptSecT A z).left) ≫ (g ▷ A).left) x ∈ (LPow A L a T).U j :=
      chart_le_res A L (g ▷ A) (whiskerRight_snd g A) a j hP'
    have e : ((𝟙 T'.left ≫ (ptSecT A z).left) ≫ (g ▷ A).left) ≫ (fst T A).left = 𝟙 T'.left ≫ g.left := by
      rw [Category.id_comp, Category.id_comp, ← Over.comp_left, ← Over.comp_left]
      congr 1
      simp [ptSecT]
    have t : ∀ s : LB.Sec (LPow A L a T'), gs (𝟙 _) x _
        ((T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j))) =
        gs (𝟙 _ ≫ (ptSecT A z).left) x _ (s.f j) := fun s =>
      (gs_res (𝟙 _) x (val_le A L z j) hx _).trans (gs_pull (𝟙 _) (ptSecT A z).left x _ hP (s.f j))
    refine (t F₂).trans ((GermD.pullSec_stalk A L a h₂ _ x j hP').trans ?_)
    refine Eq.trans ?_ (gs_mul (𝟙 _) x _ hx _ _).symm
    refine (congrArg (gs _ x _) (hF j)).trans ((gs_mul _ x _ hQ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
    · refine (gs_liftFun A _ r _ x hQ).trans ?_
      rw [e]
      exact ((gs_res (𝟙 _) x le_top hx _).trans (gs_pull (𝟙 _) g.left x ⊤ trivial r)).symm
    · exact ((t F₁).trans (GermD.pullSec_stalk A L a h₁ _ x j hP')).symm
  rw [key, hv j, map_mul]
  exact (_root_.mul_assoc _ _ _).symm

end Sec

theorem appTop_toΓ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    ((spMap f).appTop).hom (toΓ A a) = toΓ B (f a) := by
  simp only [toΓ, spMap]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end GlobalTheory.NabLinear

namespace GlobalTheory


open NabLinear in
theorem nab_smul_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (N : ℕ) (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (r : S), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) → ∀ α, nab y ((N : ℤ) ^ 2) F' α = r * nab y ((N : ℤ) ^ 2) F α := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S _ _ y N
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have key : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x))) (r : S),
      (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) →
        ∀ α, nab y K F' α = r * nab y K F α := by
    rintro K k rfl F F' r hF α
    obtain ⟨C, hex, hval⟩ := hnab.2 S y
    obtain ⟨f, hf⟩ := hex k F
    have hf' : IsGerm y C.d C.x C.B.A.act C.e C.wP k F' (MvPowerSeries.C r * f) := by
      intro m
      obtain ⟨F₁, τ, hP, hC, hV⟩ := hf m
      obtain ⟨F₂, hP₂⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
        (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F'
      refine ⟨F₂, τ, hP₂, hC, ?_⟩
      have h := isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (jBase y C.d m 1) hF hP hP₂ hV
      refine (congrArg (IsValueAt Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) F₂ (C.x m) τ) ?_).mp h
      refine (congrArg (fun w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤) => w * toΓ _ (psJet m f))
        (appTop_toΓ (algebraMap S (Jet S (Fin 1 × Fin C.d) m)) r)).trans ?_
      rw [FBIdJet.psJet_mul, psJet_C, map_mul]
    exact (hval k F' _ hf' α).trans ((nabVal_C_mul _ _ _ _ _ _ _ _).trans (congrArg (r * ·) (hval k F f hf α).symm))
  exact key _ (N ^ 2) (Nat.cast_pow N 2).symm

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VtBaseChange

theorem exists_mulTwist {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (N : ℕ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L 1 T)} {s' : LB.Sec (LPow A L 1 T')}
    (hs : IsPullSec A L 1 (h ▷ A) (whiskerRight_snd _ _) s s')
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])} (g₀ : α₀.IsGen)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1])}
    (cα : LB.Gen.Corr L _ _ _ _ α (LB.pullGen L _ _ α₀ (snd T A).left))
    {s₁ : LB.Sec (LPow A L ((N : ℤ) ^ 2) T)}
    (tw : IsTwistPull A L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁) :
    ∃ α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, (snd T' A ^ N).left] ![(N : ℤ) ^ 2, -1]),
      LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α₀ (snd T' A).left) ∧
      IsTwistPull A L (mulT A T' N) (snd T' A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α' s'
        (GlobalTheory.VVRank.pullS A ((N : ℤ) ^ 2) h s₁) := by
  have e1 : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := GlobalTheory.VVRank.whisker_snd_left A h
  have e2 : (snd T' A).left ≫ (mulA A N).left = (snd T' A ^ N).left := by
    unfold mulA
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hm0 : mulT A T' N ≫ (h ▷ A) = (h ▷ A) ≫ mulT A T N := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [mulT]
    · simp [mulT, MonObj.comp_pow]
  have hm : (mulT A T' N).left ≫ (h ▷ A).left = (h ▷ A).left ≫ (mulT A T N).left := by
    rw [← Over.comp_left, hm0, Over.comp_left]
  obtain ⟨α', gα', vα'⟩ := GlobalTheory.VVRank.exists_gen_pullTo (φ' := ![(snd T' A).left, (snd T' A ^ N).left])
    α₀ g₀ (snd T' A).left (by intro k; fin_cases k; exacts [Category.comp_id _, e2])
  refine ⟨α', ?_, ?_⟩
  · refine corr_of_val hL fun y J hJ => ?_
    rw [vα' _ (𝟙 _) y J hJ, val_pull hJ]
  · obtain rfl := GlobalTheory.TwistBaseChange.eq_pullS_of_isPullSec A 1 h hs
    refine GlobalTheory.VVRank.isTwistPull_of_sv A hL gα' fun y J hJ => ?_
    rw [GlobalTheory.VVRank.sv_pullS A _ h s₁ _ y hJ, GlobalTheory.VVRank.sv_of_isTwistPull A tw _ y hJ,
      GlobalTheory.VVRank.sv_pullS A _ h s _ y hJ, vα' _ (𝟙 _) y J hJ, val_corr hJ cα, val_pull hJ]
    simp only [Category.id_comp, e1, hm]

theorem isVtOver_isUUOver_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ) (I : Ideal (𝓞 E)) (T T' : Over Xo.X) (h : T' ⟶ T) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)) (s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T')), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) s s' → ∀ (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)) (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T')), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' → (∀ t : T ⟶ Xo.univ.t.G, IsVtOver Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo I) s t F → IsVtOver Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo I) s' (h ≫ t) F') ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s' (h ≫ x₁) (h ≫ x₂) F' := by
  intro E _ _ _ H Dw l Xo N I T T' h s s' hs F F' hF
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  refine ⟨fun t hV => ?_, fun x₁ x₂ hU => ?_⟩
  · unfold IsVtOver at hV ⊢
    obtain ⟨t₀, α₀, α, s₁, U, ht, hok, g₀, hnm, cα, tw, hsym, hact⟩ := hV
    obtain ⟨α', cα', tw'⟩ := exists_mulTwist Xo.univ.t.G hL N h hs g₀ cα tw
    obtain ⟨U', -, -, hsym', hact'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U
    refine ⟨h ≫ t₀, α₀, α', _, U', ?_, ?_, g₀, hnm, cα', tw', hsym' _ _ hsym,
      hact' _ _ _ _ hact (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₁) hF⟩
    · rw [← MonObj.comp_pow, ht]
    · unfold KilledBy at hok ⊢
      intro a ha
      rw [Category.assoc, hok a ha, MonObj.comp_one]
  · unfold IsUUOver at hU ⊢
    obtain ⟨α₀, α, s₁, s₂, U₁, U₂, g₀, hnm, cα, tw, hsym₁, hact₁, hsym₂, hact₂⟩ := hU
    obtain ⟨α', cα', tw'⟩ := exists_mulTwist Xo.univ.t.G hL N h hs g₀ cα tw
    obtain ⟨U₁', -, -, hsym₁', hact₁'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U₁
    obtain ⟨U₂', -, -, hsym₂', hact₂'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U₂
    exact ⟨α₀, α', _, _, U₁', U₂', g₀, hnm, cα', tw', hsym₁' _ _ hsym₁,
      hact₁' _ _ _ _ hact₁ (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₁) (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₂),
      hsym₂' _ _ hsym₂, hact₂' _ _ _ _ hact₂ (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₂) hF⟩

end GlobalTheory.VtBaseChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.harmonic_sum_triangular_frameChange : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = 𝟙 _ → ∀ (n : ℕ), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) = (∏ ℓ : Lt1 Dw, ((t (some ℓ) : Sˣ) : S) ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  first | exact @GlobalTheory.TriangularFrame.harmonic_sum_frBor | exact GlobalTheory.TriangularFrame.harmonic_sum_frBor | (intros; apply GlobalTheory.TriangularFrame.harmonic_sum_frBor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isRawChart_baseChange_jetPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (uvec : Lt1 Dw → Fin d → S), RIsChart x0 u d F act uvec x → RIsChart (spMap ψ ≫ x0) (fun τ i => spMap (dualMap ψ) ≫ u τ i) d (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (fun ℓ j => ψ (uvec ℓ j)) x' := by
  first | exact @GlobalTheory.RawChartBC.rIsChart_baseChange | exact GlobalTheory.RawChartBC.rIsChart_baseChange | (intros; apply GlobalTheory.RawChartBC.rIsChart_baseChange <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.connection_linear_in_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (N : ℕ) (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (r : S), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) → ∀ α, nab y ((N : ℤ) ^ 2) F' α = r * nab y ((N : ℤ) ^ 2) F α := by
  first | exact @GlobalTheory.nab_smul_section | exact GlobalTheory.nab_smul_section | (intros; apply GlobalTheory.nab_smul_section <;> assumption)

end
end
