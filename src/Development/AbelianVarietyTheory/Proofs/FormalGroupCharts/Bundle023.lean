module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle022
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005

@[expose] public section

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.BilAdd

variable {k : Type} [CommRing k] {d : ℕ}

theorem hasSubst_pts {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    MvPowerSeries.HasSubst (fun p : Fin l × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2

theorem ev_add {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f g : PS k l d) :
    ev a (f + g) = ev a f + ev a g :=
  MvPowerSeries.subst_add (hasSubst_pts a h) f g

theorem ev_pt {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (j : Fin l) (i : Fin d) :
    ev a (pt k d j i) = a j i :=
  MvPowerSeries.subst_X (hasSubst_pts a h) (j, i)

theorem ev_ev {n l r : ℕ} (a : Fin l → Pt k n d) (b : Fin n → Pt k r d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0)
    (f : PS k l d) : ev b (ev a f) = ev (fun j i => ev b (a j i)) f :=
  MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f

theorem const_pt {n : ℕ} (j : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt k d j i) = 0 :=
  MvPowerSeries.constantCoeff_X _

theorem ev_id {n : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f := by
  have := MvPowerSeries.subst_self (σ := Fin n × Fin d) (R := k)
  exact congrFun this f

def degIn (j : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) : ℕ := ∑ i, e (j, i)

theorem coeff_double (j : Fin 2) (g : PS k 2 d) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) =
      2 ^ degIn j e * MvPowerSeries.coeff e g := by
  have h : ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g =
      MvPowerSeries.rescale (fun p : Fin 2 × Fin d => if p.1 = j then (2 : k) else 1) g := by
    rw [MvPowerSeries.rescale_eq_subst]
    unfold ev
    congr 1
    funext p
    by_cases hp : p.1 = j
    · subst hp
      simp [pt, two_smul]
    · simp [hp, pt]
  rw [h, MvPowerSeries.coeff_rescale]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type, degIn, ← Finset.prod_pow_eq_pow_sum,
    Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem eq_zero_of_double [Algebra ℚ k] {a : ℕ} (ha : a ≠ 1) {c : k} (h : 2 ^ a * c = c + c) : c = 0 := by
  have h0 : ((2 : ℚ) ^ a - 2) ≠ 0 := by
    intro h
    apply ha
    have : (2 : ℚ) ^ a = 2 ^ 1 := by linarith
    exact (pow_right_injective₀ (by norm_num) (by norm_num)) this
  have hu : IsUnit ((2 : k) ^ a - 2) := by
    have := (IsUnit.mk0 _ h0).map (algebraMap ℚ k)
    simpa [map_ofNat] using this
  apply hu.mul_right_eq_zero.mp
  linear_combination h

theorem exists_single {e : Fin 2 × Fin d →₀ ℕ} (h0 : degIn 0 e = 1) (h1 : degIn 1 e = 1) :
    ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 := by
  have key : ∀ f : Fin d → ℕ, ∑ i, f i = 1 → ∃ i, ∀ i', f i' = if i = i' then 1 else 0 := by
    intro f hf
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hf
    refine ⟨i, fun i' => ?_⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hf
    split_ifs with h
    · subst h
      omega
    · have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨fun hh => h hh.symm, Finset.mem_univ i'⟩ : i' ∈ Finset.univ.erase i)
      omega
  obtain ⟨i, hi⟩ := key _ h0
  obtain ⟨j, hj⟩ := key _ h1
  refine ⟨i, j, ?_⟩
  ext ⟨l, p⟩
  fin_cases l
  · simp [hi, Finsupp.single_apply]
  · simp [hj, Finsupp.single_apply]

theorem coeff_bilSer (β : Matrix (Fin d) (Fin d) k) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (bilSer β (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      ∑ i, ∑ j, if e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 then β i j else 0 := by

  simp only [bilSer, map_sum, pt, MvPowerSeries.coeff_C_mul, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial,
  MvPowerSeries.coeff_monomial]
  simp

theorem single_inj {i j i' j' : Fin d}
    (h : (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 : Fin 2 × Fin d →₀ ℕ) =
      Finsupp.single ((0 : Fin 2), i') 1 + Finsupp.single ((1 : Fin 2), j') 1) : i = i' ∧ j = j' := by
  have h0 := DFunLike.congr_fun h (0, i)
  have h1 := DFunLike.congr_fun h (1, j)
  simp [Finsupp.single_apply] at h0 h1
  exact ⟨h0.symm, h1.symm⟩

theorem jeq_bil_of_double [Algebra ℚ k] (m : ℕ) (g : PS k 2 d)
    (h : ∀ j : Fin 2, JEq m (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) (g + g)) :
    JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g)
      (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  intro e he
  refine Eq.trans ?_ (coeff_bilSer _ e).symm
  by_cases hex : ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1
  · obtain ⟨i, j, rfl⟩ := hex
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j, if_pos rfl]
    · intro b _ hb
      exact if_neg fun hh => hb (single_inj hh).2.symm
    · simp
    · intro b _ hb
      exact Finset.sum_eq_zero fun c _ => if_neg fun hh => hb (single_inj hh).1.symm
    · simp
  · have hz : MvPowerSeries.coeff e g = 0 := by
      have : ∃ j, degIn j e ≠ 1 := by
        by_contra hc
        push Not at hc
        exact hex (exists_single (hc 0) (hc 1))
      obtain ⟨j, hj⟩ := this
      have := h j e he
      rw [coeff_double, map_add (f := _)] at this
      exact eq_zero_of_double hj this
    rw [hz]
    symm
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => if_neg fun hh => hex ⟨i, j, hh⟩

theorem ev_pair (b : Fin 3 → Pt k 2 d) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0) (g : PS k 2 d)
    (u v : Pt k 3 d) (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) :
    ev b (ev ![u, v] g) = ev ![fun i => ev b (u i), fun i => ev b (v i)] g := by
  rw [ev_ev _ _ _ hb]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j i
    fin_cases j
    · exact hu i
    · exact hv i

theorem jeq_bilSer_of_biadditive : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d m : ℕ) (g : PS k 2 d), JEq m (ev (n := 3) ![pt k (n := 3) d 0 + pt k (n := 3) d 1, pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] g) → JEq m (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1 + pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] g + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g) → JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  intro k _ _ d m g h1 h2
  have hsub := (GlobalTheory.ChartCmp.JCalc.jeq_calculus k m).2.2.2.1
  have hid : ev (n := 2) ![pt k (n := 2) d 0, pt k (n := 2) d 1] g = g := by
    refine Eq.trans ?_ (ev_id g)
    congr 1
    funext j
    fin_cases j <;> rfl
  have hc : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff (pt k (n := 3) d s i) = 0 := fun s i => const_pt s i
  have hc2 : ∀ (s t : Fin 3) i, MvPowerSeries.constantCoeff ((pt k (n := 3) d s + pt k (n := 3) d t) i) = 0 := by
    intro s t i
    simp [hc]
  apply jeq_bil_of_double
  intro j
  fin_cases j
  · have hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff
        ((![pt k (n := 2) d 0, pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by
      intro s i
      fin_cases s <;> exact const_pt _ _
    have := hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h1
    rw [ev_add _ hb, ev_pair _ hb _ _ _ (hc2 _ _) (hc _), ev_pair _ hb _ _ _ (hc _) (hc _),
      ev_pair _ hb _ _ _ (hc _) (hc _)] at this
    simp only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this
    convert this using 2
    · funext l
      fin_cases l <;> rfl
    · exact hid.symm
    · exact hid.symm
  · have hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff
        ((![pt k (n := 2) d 0, pt k (n := 2) d 1, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by
      intro s i
      fin_cases s <;> exact const_pt _ _
    have := hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h2
    rw [ev_add _ hb, ev_pair _ hb _ _ _ (hc _) (hc2 _ _), ev_pair _ hb _ _ _ (hc _) (hc _),
      ev_pair _ hb _ _ _ (hc _) (hc _)] at this
    simp only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this
    convert this using 2
    · funext l
      fin_cases l <;> rfl
    · exact hid.symm
    · exact hid.symm

end GlobalTheory.ChartCmp.BilAdd
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), ∃ ψ : t.G ≅ t'.G, ψ.hom.left = n.φ ∧ IsMonHom ψ.hom ∧ (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) ∧ n.cm.F3 = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ∧ ∃ w : LB.Iso t.PP.L (t'.PP.L.pull n.φ), CubIso n w := by
  first | exact @GlobalTheory.ChartCmp.exists_iso_of_sabMap_id | exact GlobalTheory.ChartCmp.exists_iso_of_sabMap_id | (intros; apply GlobalTheory.ChartCmp.exists_iso_of_sabMap_id <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.isCanonicalGauge_sub_biadditive : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by
  first | exact @GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub | exact GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub | (intros; apply GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.jetEq_formalExp_iff_and_exists_log : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d m : ℕ), (∀ f g : PS k n d, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff g = 0 → (JEq m f g ↔ JEq m (FB.expS k f) (FB.expS k g))) ∧ ∀ u : PS k n d, MvPowerSeries.constantCoeff u = 1 → ∃ lam : PS k n d, MvPowerSeries.constantCoeff lam = 0 ∧ FB.expS k lam = u := by
  first | exact @GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log | exact GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log | (intros; apply GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.jetFrames_differ_by_unit_each_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → ∀ m, ∃ ε : PS V 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧ FrRel t x x' e e' φ m ε := by
  first | exact @GlobalTheory.ChartCmp.FrameRatio.main | exact GlobalTheory.ChartCmp.FrameRatio.main | (intros; apply GlobalTheory.ChartCmp.FrameRatio.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.localChartDepth_eq_integralBiextDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), letI := io.toAlgebra; ∀ BT : FB T.V (chD C.ch) (𝓞 E), BT.FK T.Fr = C.ch.B.FK T.Fr → (∀ a, BT.actK T.Fr a = C.ch.B.actK T.Fr a) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuAlg Dw T BT C.ch.h C.ch.uvec e k a n := by
  first | exact @GlobalTheory.ChartCmp.nuLocC_eq_nuAlg | exact GlobalTheory.ChartCmp.nuLocC_eq_nuAlg | (intros; apply GlobalTheory.ChartCmp.nuLocC_eq_nuAlg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.mvPowerSeriesJetEq_calculus : ∀ (R : Type) [CommRing R] (m : ℕ), (∀ (σ : Type) (f f' g g' : MvPowerSeries σ R), JEq m f f' → JEq m g g' → JEq m (f + g) (f' + g') ∧ JEq m (f - g) (f' - g') ∧ JEq m (f * g) (f' * g')) ∧ (∀ (σ : Type) (f g u : MvPowerSeries σ R), IsUnit (MvPowerSeries.constantCoeff u) → JEq m (f * u) (g * u) → JEq m f g) ∧ (∀ (σ R' : Type) [CommRing R'] (β : R →+* R') (f g : MvPowerSeries σ R), JEq m f g → JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g)) ∧ (∀ (d n n' : ℕ) (a a' : Fin n → Pt R n' d) (f g : PS R n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, MvPowerSeries.constantCoeff (a' i j) = 0) → (∀ i j, JEq m (a i j) (a' i j)) → JEq m f g → JEq m (ev a f) (ev a' g)) ∧ (∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R), JEq m f g ↔ psJet m f = psJet m g) ∧ (∀ (σ : Type) (f g : MvPowerSeries σ R), (∀ m', JEq m' f g) → f = g) := by
  first | exact @GlobalTheory.ChartCmp.JCalc.jeq_calculus | exact GlobalTheory.ChartCmp.JCalc.jeq_calculus | (intros; apply GlobalTheory.ChartCmp.JCalc.jeq_calculus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.carriesLinCombGenerator_calculus : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by
  first | exact @GlobalTheory.ChartCmp.carries_calculus | exact GlobalTheory.ChartCmp.carries_calculus | (intros; apply GlobalTheory.ChartCmp.carries_calculus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameBCGen

theorem cφG_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {T T' : Over X0} (ρ : T' ⟶ T) (a b : T ⟶ t.G) :
    cφG t ![ρ ≫ a, ρ ≫ b] = fun I => ρ.left ≫ cφG t ![a, b] I := by
  funext I
  refine Eq.symm (congrArg (fun q => q.left) ((psum_hom (preHom ρ) ![a, b] I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_))))
  fin_cases i <;> rfl

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t x1 d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 h01 d x x' hx e he
  subst h01
  let ρ : ∀ m, jOG (spMap ψ ≫ x0) d m 2 ⟶ jOG x0 d m 2 := fun m =>
    Over.homMk (spMap (jetCoef ψ (Fin 2 × Fin d) m)) (by
      show spMap (jetCoef ψ (Fin 2 × Fin d) m) ≫ spMap (algebraMap S (Jet S (Fin 2 × Fin d) m)) ≫ x0 =
        spMap (algebraMap S' (Jet S' (Fin 2 × Fin d) m)) ≫ spMap ψ ≫ x0
      rw [← Category.assoc, ← Category.assoc, RawFrameBC.spMap_comp_eq, RawFrameBC.spMap_comp_eq, JetTr.jetCoef_alg])
  have hp : ∀ m (i : Fin 2), jptG t (spMap ψ ≫ x0) d x' m i = ρ m ≫ jptG t x0 d x m i := by
    intro m i
    apply Over.OverMorphism.ext
    show spMap (jetCopy (S := S') d m i).toRingHom ≫ (x' m).left =
      spMap (jetCoef ψ (Fin 2 × Fin d) m) ≫ spMap (jetCopy (S := S) d m i).toRingHom ≫ (x m).left
    rw [hx, ← Category.assoc, ← Category.assoc, RawFrameBC.spMap_comp_eq, RawFrameBC.spMap_comp_eq]
    exact congrArg (fun f => spMap f ≫ (x m).left) (JetTr.jetCoef_copy ψ d m 2 i).symm
  have key := fun m => RawFrameBC.exists_reindexed_pull t.PP.isLB
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (he m) (ρ m).left
    (cφG t ![jptG t (spMap ψ ≫ x0) d x' m (0 : Fin 2), jptG t (spMap ψ ≫ x0) d x' m (1 : Fin 2)])
    (by rw [hp, hp, cφG_comp])
  choose e' h₁ h₂ _ using key
  exact ⟨e', h₁, h₂⟩

end GlobalTheory.FrameBCGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.exists_cubeFrames_from_pullback_triple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  first | exact @GlobalTheory.Chart.FrameUp.exists_frames_up | exact GlobalTheory.Chart.FrameUp.exists_frames_up | (intros; apply GlobalTheory.Chart.FrameUp.exists_frames_up <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.JetPointBC

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

section Maps

variable {X0 : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0)

def baseMap : overAt (spMap ψ ≫ x0) S' ⟶ overAt x0 S :=
  Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap S S) ≫ x0 = spMap (algebraMap S' S') ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]
    first | done | rfl)

def jetPtMap (d m n : ℕ) : jOG (spMap ψ ≫ x0) d m n ⟶ jOG x0 d m n :=
  Over.homMk (spMap (jetCoef ψ (Fin n × Fin d) m)) (by
    show spMap (jetCoef ψ (Fin n × Fin d) m) ≫ spMap (algebraMap S _) ≫ x0 =
      spMap (algebraMap S' _) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap, JetTr.jetCoef_alg])

theorem sq_aug (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ jetPtMap ψ x0 d m 1 =
      baseMap ψ x0 ≫ homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap ψ ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_aug ψ _ m)

theorem sq_subst {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ jetPtMap ψ x0 d m n =
      jetPtMap ψ x0 d m n' ≫
        homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap (jetCoef ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_substP ψ m φ).symm

theorem sq_copy (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        jetPtMap ψ x0 d m 1 =
      jetPtMap ψ x0 d m n ≫
        homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap (jetCoef ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_copy ψ d m n i).symm

end Maps

theorem unit_law_act_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) → (∀ m, homAt x1 (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) → (∀ m, homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (F p.2))) ≫ x' m = jptG t x1 d x' m (0 : Fin 2) * jptG t x1 d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) → (∀ m (b : 𝓞 E), x' m ≫ t.act.act b = homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (act b p.2))) ≫ x' m) := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 hx1 d x x' hx'
  subst hx1
  obtain rfl : x' = fun m => jetPtMap ψ x0 d m 1 ≫ x m :=
    funext fun m => Over.OverMorphism.ext (hx' m)
  refine ⟨fun h m => ?_, fun F _ h m => ?_, fun act _ h m b => ?_⟩
  · rw [← Category.assoc, sq_aug, Category.assoc, h m]
    simp [Hom.one_def]
  · simp only [JetTr.psTrunc_map]
    rw [← Category.assoc, sq_subst, Category.assoc, h m]
    simp only [jptG, Hom.mul_def, comp_lift_assoc]
    rw [← Category.assoc (homAt _ _) (jetPtMap _ _ _ _ _), ← Category.assoc (homAt _ _) (jetPtMap _ _ _ _ _),
      sq_copy, sq_copy, Category.assoc, Category.assoc]
  · simp only [JetTr.psTrunc_map]
    rw [← Category.assoc (homAt _ _), sq_subst, Category.assoc, Category.assoc, h m b]

end GlobalTheory.JetPointBC
end
end
