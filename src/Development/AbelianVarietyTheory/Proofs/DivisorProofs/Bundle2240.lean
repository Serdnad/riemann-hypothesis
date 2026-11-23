module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

theorem exists_equiv_reps {G : Type} [Group G] (Γ Λ : Subgroup G) (T : Set Γ)
    (hT : ∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ) (γ : Γ) :
    ∃ π : T ≃ T, ∀ i : T, ((i.1 * γ * (π i).1⁻¹ : Γ) : G) ∈ Λ := by
  choose ρ hρ hu using hT
  have key : ∀ (a b : Γ), a * b = 1 → ∀ i : T, ρ (ρ (i.1 * a) * b) = i.1 := by
    intro a b hab i
    symm
    refine hu _ _ ⟨i.2, ?_⟩
    have := Λ.inv_mem (hρ (i.1 * a)).2
    have e : ρ (i.1 * a) * b * i.1⁻¹ = (i.1 * a * (ρ (i.1 * a))⁻¹)⁻¹ := by
      rw [eq_inv_of_mul_eq_one_right hab]; group
    rw [e, Subgroup.coe_inv]
    exact this
  exact ⟨⟨fun i => ⟨ρ (i.1 * γ), (hρ _).1⟩, fun i => ⟨ρ (i.1 * γ⁻¹), (hρ _).1⟩,
    fun i => Subtype.ext (key γ γ⁻¹ (mul_inv_cancel _) i), fun i => Subtype.ext (key γ⁻¹ γ (inv_mul_cancel _) i)⟩,
    fun i => (hρ _).2⟩

theorem reps_perm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → ∀ T, IsReps σ J (col X) T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ lineGrp σ J (col X)), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ lineGrp σ J (col X)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D T hT
  have h3 : ∀ γ ∈ (ratPts σ J ⊓ lineGrp σ J (col X)), ∀ g, h (γ * g) = h g := by
    rintro γ ⟨hγ, l, hl⟩ g
    rw [(GlobalTheory.T.height_function_scaling_parabolic F E σ n J r X Y L a h D).2 γ l hl g,
      (GlobalTheory.T.levi_normalizes_unipotent_radical_bis F E σ n J r X Y D.cm D.herm D.witt).2.2.2.2.2 γ hγ l hl]
    simp
  have h4 : ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ lineGrp σ J (col X)) := by
    intro γ
    obtain ⟨t, ⟨ht, hl⟩, hu⟩ := hT γ
    exact ⟨t, ⟨ht, (γ * t⁻¹).2, hl⟩, fun s hs => hu s ⟨hs.1, hs.2.2⟩⟩
  refine ⟨fun γ hγ => ?_, ?_, h3, h4⟩
  · obtain ⟨π, hπ⟩ := exists_equiv_reps _ _ T h4 ⟨γ, hγ⟩
    refine ⟨π, fun i g => ?_⟩
    rw [← h3 _ (hπ i) ((π i).1.1 * g)]
    congr 1
    simp [mul_assoc]
  · obtain ⟨t, ⟨ht, hl⟩, -⟩ := h4 1
    refine ⟨⟨t, ht⟩, fun g => ?_⟩
    rw [← h3 _ hl (t.1 * g)]
    congr 1
    simp

end GlobalTheory.ResLine
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem modulus_mul_measure_shell_le : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ C : Set G, IsCompact C → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (b : G) (κ : ℝ≥0∞), (∀ m ∈ M, b * m = m * b) → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → ∀ S : Set G, MeasurableSet S → (∀ x ∈ S, ∃ u ∈ N, ∃ m ∈ M, ∃ y ∈ C, b * x = u * m * y) → κ * μ (S ∩ D) ≤ B := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM hL μ D hμ hD C hC
  obtain ⟨U, c, hU, hμU, hc, hlow⟩ := GlobalTheory.T.semidirectAverage_indicator_lower_bound G N M Λ ν π DN DM hL μ hμ C hC
  have hX : ν DN * π DM * μ U ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hL.finN hL.finM) hμU
  refine ⟨ν DN * π DM * μ U / c, ENNReal.div_ne_top hX hc, ?_⟩
  intro b κ hb hκ S hS hSx
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inr hX)]
  have hφ : Measurable (U.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have hw := GlobalTheory.T.lintegral_two_step_unfolding_semidirect_lattice G N M Λ ν π DN DM hL μ D hμ hD
    (fun x => U.indicator (1 : G → ℝ≥0∞) (b * x)) (hφ.comp (measurable_const_mul b))
  rw [lintegral_mul_left_eq_self (U.indicator (1 : G → ℝ≥0∞)) b,
    lintegral_indicator_one hU.measurableSet] at hw
  rw [← hw]
  have h1 : κ * μ (S ∩ D) * c = ∫⁻ x in D, S.indicator (fun _ => κ * c) x ∂μ := by
    rw [lintegral_indicator_const hS, Measure.restrict_apply hS]; ring
  rw [h1]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    obtain ⟨u₀, hu₀, m₀, hm₀, y, hy, hxy⟩ := hSx x hx
    have h2 := hlow u₀ hu₀ m₀ hm₀ y hy
    rw [← hxy] at h2
    refine le_trans (mul_le_mul_right h2 κ) (le_trans (lintegral_const_mul_le _ _) (le_of_eq ?_))
    refine lintegral_congr fun m => ?_
    have h3 := hκ (fun g => U.indicator (1 : G → ℝ≥0∞) (g * m * (b * x)))
      (hφ.comp ((measurable_id.mul_const _).mul_const _))
    rw [← h3]
    refine lintegral_congr fun u => ?_
    congr 1
    have h4 := hb m m.2
    calc b * (u : G) * b⁻¹ * m * (b * x) = b * u * b⁻¹ * (m * b) * x := by group
      _ = b * u * b⁻¹ * (b * m) * x := by rw [h4]
      _ = b * (u * m * x) := by group
  · rw [Set.indicator_of_notMem hx]; exact zero_le

end GlobalTheory.ResLine
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_groupAlgebra_action_of_commute_order : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) → ∃ y, actOn L.rep (AfP p) y = A := by
  first | (exact @GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute) | (exact GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute) | (intros; apply GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

theorem _root_.GlobalTheory.T.pairing_adjoint_involution : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  first | (exact @GlobalTheory.LKGeo.adj_actOn_afP) | (exact GlobalTheory.LKGeo.adj_actOn_afP) | (intros; apply GlobalTheory.LKGeo.adj_actOn_afP  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lattice_pairing_integral : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (v w : AfP p ⊗[ℚ] VQ D), v ∈ LaHat D → w ∈ LaHat D → IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) v w) := by
  first | (exact @GlobalTheory.LKGeo.formInt_laHat) | (exact GlobalTheory.LKGeo.formInt_laHat) | (intros; apply GlobalTheory.LKGeo.formInt_laHat  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

open GlobalTheory.Frames

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.CompHS

theorem der_fun_hor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hQ : KSIso (psiSet H) Q) (hz : z ≫ toFlag M = X.ptY Q)
    {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)} (hv : IsTanFrame (psiSet H) Q v)
    {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} (hw : IsDef Q w) {Mx : HIx Dw (psiSet H) → K}
    (hM : GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x Mx) {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w), ∃ C : VIx Dw → K, ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O),
      (evalPt zw O hzw g).snd = ∑ k, Mx k * (evalPt (zv (.inl k)) O (hzv _) g).snd +
        ∑ k, C k * (evalPt (zv (.inr k)) O (hzv _) g).snd := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ _ z ho Q hQ hz v hv zv hl w hw Mx hM zw hlw
  obtain ⟨W, zM, hzM⟩ := hQ.exists_universal
  have hWQ : FrMap (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)) W Q :=
    GlobalTheory.FlagTan.frMap_comp (hzM 0).1 (hzM 0).2.1 fun a => by simp
  obtain ⟨ZW, hZW⟩ := FunDer.der_dir M hz ho hWQ
  choose zz hzz using fun k : GlobalTheory.FlagTan.FIx Dw => (GlobalTheory.FlagTan.existsUnique_isVert Q (Pi.single k (1 : K))).exists
  choose q hq hqO using fun k => exists_tanLift M (hzz k).isDef hz ho
  have key : ∀ (w' : FrPt Xo c (DualNumber K)) (M' : HIx Dw (psiSet H) → K), IsDef Q w' →
      GlobalTheory.FlagTan.IsKS (psiSet H) Q w'.x M' → ∃ C : VIx Dw → K, ∀ (p : Sp (DualNumber K) ⟶ M.X),
        p ≫ toFlag M = X.ptY w' → ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hp : ⊤ ≤ p ⁻¹ᵁ O)
        (hzv : ∀ k : VIx Dw, ⊤ ≤ zv (.inr k) ⁻¹ᵁ O), ∃ hZ : ⊤ ≤ ZW ⁻¹ᵁ O,
          (evalPt p O hp g).snd = ∑ k, (evalPt ZW O hZ g).snd k * M' k +
            ∑ k, C k * (evalPt (zv (.inr k)) O (hzv k) g).snd := by
    intro w' M' hw' hM'
    obtain ⟨N, hN⟩ := (hzM M').2.1.exists_isShift hw'
      (hQ.injective hw'.isTanX (hzM M').2.1.isTanX hM' (hzM M').2.2)
    obtain ⟨p₀, hp₀, hp₀O⟩ := exists_tanLift M (hzM M').2.1 hz ho
    refine ⟨fun k => N k.toF, fun p hp O g hpO hzv => ?_⟩
    have hzO : ⊤ ≤ z ⁻¹ᵁ O := by
      rw [← FunDer.red_eq M hz ho hw' hp]
      exact FunDer.top_le_comp _ _ _ hpO
    obtain ⟨hZ, a0⟩ := hZW M' _ p₀ (hzM M').1 hp₀ O g (hp₀O O hzO)
    refine ⟨hZ, ?_⟩
    rw [FunDer.der_shift M hz ho (hzM M').2.1 hN hzz hp₀ hp hq O g (hp₀O O hzO) hpO (fun k => hqO k O hzO), a0,
      GlobalTheory.FlagTan.sum_FIx]
    congr 1
    have hz0 : ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range GlobalTheory.FlagTan.VIx.toF),
        N k * (evalPt (q k) O (hqO k O hzO) g).snd = 0 :=
      Finset.sum_eq_zero fun k hk => by
        have hN' : ∀ σ i j, i < j → (Pi.single k (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ, i, j⟩) = 0 :=
          fun σ i j hij => by
            refine Pi.single_eq_of_ne ?_ _
            rintro rfl
            exact (Finset.mem_filter.1 hk).2 ⟨⟨σ, (i, j), hij⟩, rfl⟩
        rw [FunDer.der_vert_eq_zero M hz ho (hzz k) hN' (hq k) O g _, mul_zero]
    rw [hz0, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : zz k.toF = v (.inr k) :=
      (GlobalTheory.FlagTan.existsUnique_isVert Q _).unique (hzz k.toF) (hv.2 k)
    have e2 : q k.toF = zv (.inr k) := FunDer.lift_eq M (by rw [hq, hl, e1]) (hqO _ _ ho)
    rw [FunDer.evalPt_eq_of_eq e2 O _ (hzv k) g]
  obtain ⟨C, hC⟩ := key w Mx hw hM
  choose C' hC' using fun k => key _ _ (hv.1 k).1 (hv.1 k).2
  refine ⟨fun j => C j - ∑ k, Mx k * C' k j, fun O g hzw hzvO => ?_⟩
  obtain ⟨hZ, a⟩ := hC zw hlw O g hzw (fun k => hzvO _)
  have b : ∀ k, (evalPt (zv (.inl k)) O (hzvO _) g).snd =
      (evalPt ZW O hZ g).snd k + ∑ j, C' k j * (evalPt (zv (.inr j)) O (hzvO _) g).snd := fun k => by
    obtain ⟨hZ', b⟩ := hC' k (zv (.inl k)) (hl _) O g (hzvO _) (fun j => hzvO _)
    rw [b]
    simp [Pi.single_apply]
  rw [a, Finset.sum_congr rfl fun k _ => congrArg (Mx k * ·) (b k)]
  simp only [mul_add, Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (VIx Dw)))]
  simp only [mul_comm _ (Mx _)]
  ring

end GlobalTheory.CompHS
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ ∀ v ∈ LaHat D, j • A v ∈ LaHat D := by
  first | (exact @GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem) | (exact GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem) | (intros; apply GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integralAdeleLimit_compatibleIntSystem : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) → ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := by
  first | (exact @GlobalTheory.CompatLim.exists_lim) | (exact GlobalTheory.CompatLim.exists_lim) | (intros; apply GlobalTheory.CompatLim.exists_lim  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.degree_supLattice_component_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, (h.data f₁ f₂ th k).degM j = GlobalTheory.AllWt.degOn U x V dict Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0) := by
  first | exact @GlobalTheory.CompHS.Ready.degM_eq | exact GlobalTheory.CompHS.Ready.degM_eq | (intros; apply GlobalTheory.CompHS.Ready.degM_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁) (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ {ι : Type} [Fintype ι] (d : ι → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → ∀ (Mx : ι → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →+* K) (hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K), X.F.ChartFr k _ hk Q → ∀ (θ : Γ(M.X, W₁) →+* DualNumber K) (m : ι → K), (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * ψ (d a s).snd) → ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (∑ a, m a • (ψ ∘ Mx a)) ∧ spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.HorFrame.exists_deform_of_comb | exact GlobalTheory.HorFrame.exists_deform_of_comb | (intros; apply GlobalTheory.HorFrame.exists_deform_of_comb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.cmObjHomOfType_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q)
    (x : Fin p → 𝓞 E), ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) = 1 → x = 0 := by
  first | exact @GlobalTheory.FlatCM.HomIndep.phiP_independent | exact GlobalTheory.FlatCM.HomIndep.phiP_independent | (intros; apply GlobalTheory.FlatCM.HomIndep.phiP_independent <;> assumption)
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem _root_.GlobalTheory.T.maximalCompact_archOperator_preserves_fockVacua : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ g : SInf F (Fin n × Fin d), GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb g → GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb (A g) := by
  first | exact @GlobalTheory.KInfVac.gaussD_of_kInf | exact GlobalTheory.KInfVac.gaussD_of_kInf | (intros; apply GlobalTheory.KInfVac.gaussD_of_kInf <;> assumption)
end
