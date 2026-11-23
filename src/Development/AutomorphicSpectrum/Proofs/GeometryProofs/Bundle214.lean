module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle029
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle209
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle210
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle208
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isConnected_zeroSet_of_isProper : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) :=
  @PositivityTheory.Xgn.zero_set_special_fibre_connected

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl.TorsChart

theorem alg {R : Type*} [CommRing R] (t s : R) (g g' a r v : Rˣ) (N n : ℕ)
    (h : t * ((g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a).val * (g * r).val ^ (N ^ 2)) ^ n =
      ((g' ^ (n : ℤ)).val * s) ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n) :
    t * (a.val * r.val ^ (N ^ 2)) ^ n = s ^ (N ^ 2) * v.val ^ n := by
  have hz : ∀ u : Rˣ, u ^ (-((N : ℤ) ^ 2)) = (u ^ (N ^ 2))⁻¹ := fun u => by
    rw [zpow_neg, ← zpow_natCast]; push_cast; rfl
  have e₁ : g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a * (g * r) ^ (N ^ 2) = g * (a * r ^ (N ^ 2)) := by
    rw [hz, zpow_one, mul_pow]
    calc g * (g ^ (N ^ 2))⁻¹ * a * (g ^ (N ^ 2) * r ^ (N ^ 2))
        = g * (a * r ^ (N ^ 2)) * ((g ^ (N ^ 2))⁻¹ * g ^ (N ^ 2)) := by ac_rfl
      _ = _ := by rw [inv_mul_cancel, _root_.mul_one]
  have e₂ : ((g' ^ (n : ℤ)) ^ (N ^ 2)) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v) ^ n = g ^ n * v ^ n := by
    rw [hz, zpow_one, zpow_natCast, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n]
    calc g' ^ (N ^ 2 * n) * (g ^ n * (g' ^ (N ^ 2 * n))⁻¹ * v ^ n)
        = g ^ n * v ^ n * (g' ^ (N ^ 2 * n) * (g' ^ (N ^ 2 * n))⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel, _root_.mul_one]
  have l : (g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a).val * (g * r).val ^ (N ^ 2) = g.val * (a.val * r.val ^ (N ^ 2)) := by
    have := congrArg Units.val e₁
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have m : (g' ^ (n : ℤ)).val ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n = g.val ^ n * v.val ^ n := by
    have := congrArg Units.val e₂
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  rw [l] at h
  apply (g ^ n).isUnit.mul_right_inj.1
  simp only [Units.val_pow_eq_pow_val]
  calc g.val ^ n * (t * (a.val * r.val ^ (N ^ 2)) ^ n)
      = t * (g.val * (a.val * r.val ^ (N ^ 2))) ^ n := by rw [mul_pow g.val]; ring
    _ = _ := h
    _ = ((g' ^ (n : ℤ)).val ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n) * s ^ (N ^ 2) := by
        rw [mul_pow (g' ^ (n : ℤ)).val]; ring
    _ = g.val ^ n * v.val ^ n * s ^ (N ^ 2) := by rw [m]
    _ = _ := by ring

variable {F : Type} [Field F] {X S : Scheme.{0}}

theorem charts {L : LB X} {q : X ⟶ X} {e : S ⟶ X} {b : Sp F ⟶ S} {o y : Sp F ⟶ X}
    (hbe : b ≫ e = o) (hoq : o ≫ q = o) (hyq : y ≫ q = o) {n N : ℕ}
    (w : LB.Gen (LB.LinComb L (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => e) (fun _ => 1))) (hr : rig.IsGen)
    (s : Out.H0 L n) (T : F) (i₀ i : L.ι) (h₀ : ⊤ ≤ o ⁻¹ᵁ L.U i₀) (hi : ⊤ ≤ y ⁻¹ᵁ L.U i)
    (hE : T * (valF o _ (w.s ![i₀, i₀]).val * valF b _ (rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n =
      valF y _ (s.f fun _ => i) ^ (N ^ 2) * valF y _ (w.s ![i₀, i]).val ^ n)
    (z : Sp F) (J : (Sp F ⟶ X) → L.ι) (hJ : Good L z J) :
    toStk z T * ((val w o z J).val * (val rig b z J).val ^ (N ^ 2)) ^ n =
      sval s y z J ^ (N ^ 2) * (val w y z J).val ^ n := by
  have m₀ : o z ∈ L.U i₀ := (top_le_iff_mem _ _ z).1 h₀
  have mi : y z ∈ L.U i := (top_le_iff_mem _ _ z).1 hi
  have mo : o z ∈ L.U (J o) := hJ o
  have my : y z ∈ L.U (J y) := hJ y
  have wm : ∀ (r : Sp F ⟶ X), r ≫ q = o → ∀ a c : L.ι, o z ∈ L.U a → r z ∈ L.U c →
      r z ∈ LB.wchart L (K := Fin 2) ![q, 𝟙 X] ![a, c] := by
    intro r hr' a c ha hc
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show q (r z) ∈ L.U a
      have : q (r z) = o z := by rw [← hr']; rfl
      rw [this]; exact ha
    · exact hc
  have rm : ∀ a : L.ι, o z ∈ L.U a → b z ∈ LB.wchart L (K := PUnit) (fun _ => e) (fun _ => a) := by
    intro a ha
    refine Set.mem_iInter.2 fun _ => ?_
    show e (b z) ∈ L.U a
    have : e (b z) = o z := by rw [← hbe]; rfl
    rw [this]; exact ha
  have sm : ∀ a : L.ι, y z ∈ L.U a → y z ∈ LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a) :=
    fun a ha => Set.mem_iInter.2 fun _ => ha
  have a₁ : toStk z (valF o _ (w.s ![i₀, i₀]).val) =
      (trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] o z ![i₀, i₀] ![J o, J o] *
        gm o z (LB.wchart L ![q, 𝟙 X] ![J o, J o]) (w.s ![J o, J o])).val :=
    (toStk_valF o _ z (wm o hoq _ _ m₀ m₀) _).trans
      (congrArg Units.val (gen_trans hw o z (wm o hoq _ _ m₀ m₀) (wm o hoq (J o) (J o) mo mo)))
  have a₂ : toStk z (valF b _ (rig.s fun _ => i₀).val) =
      (trF (L := L) (K := PUnit) (fun _ => e) (fun _ => 1) b z (fun _ => i₀) (fun _ => J o) *
        gm b z (LB.wchart L (fun _ => e) (fun _ => J o)) (rig.s fun _ => J o)).val :=
    (toStk_valF b _ z (rm _ m₀) _).trans (congrArg Units.val (gen_trans hr b z (rm _ m₀) (rm (J o) mo)))
  have a₃ : toStk z (valF y _ (s.f fun _ => i)) =
      (trF (L := L) (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) y z (fun _ => i) (fun _ => J y)).val *
        gs y z (LB.wchart L (fun _ => 𝟙 X) (fun _ => J y)) (s.f fun _ => J y) :=
    (GlobalTheory.ThetaInValues.toStk_valF' y _ z (sm _ mi) _).trans (sec_trans s y z (sm _ mi) (sm (J y) my))
  have a₄ : toStk z (valF y _ (w.s ![i₀, i]).val) =
      (trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] y z ![i₀, i] ![J o, J y] *
        gm y z (LB.wchart L ![q, 𝟙 X] ![J o, J y]) (w.s ![J o, J y])).val :=
    (toStk_valF y _ z (wm y hyq _ _ m₀ mi) _).trans
      (congrArg Units.val (gen_trans hw y z (wm y hyq _ _ m₀ mi) (wm y hyq (J o) (J y) mo my)))
  have hE' := congrArg (toStk z) hE
  simp only [map_mul, map_pow] at hE'
  rw [a₁, a₂, a₃, a₄] at hE'
  have f₁ : trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] o z ![i₀, i₀] ![J o, J o] =
      gm o z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm o z _ (L.g i₀ (J o)) ^ (-((N : ℤ) ^ 2)) := by
    rw [trF, Fin.prod_univ_two]
    show gm (o ≫ q) z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm (o ≫ 𝟙 X) z _ (L.g i₀ (J o)) ^ (-((N : ℤ) ^ 2)) = _
    rw [hoq, Category.comp_id]
  have f₂ : trF (L := L) (K := PUnit) (fun _ => e) (fun _ => 1) b z (fun _ => i₀) (fun _ => J o) =
      gm o z _ (L.g i₀ (J o)) := by
    rw [trF, Fintype.prod_unique]
    show gm (b ≫ e) z _ (L.g i₀ (J o)) ^ (1 : ℤ) = _
    rw [hbe, zpow_one]
  have f₃ : trF (L := L) (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) y z (fun _ => i) (fun _ => J y) =
      gm y z _ (L.g i (J y)) ^ (n : ℤ) := by
    rw [trF, Fintype.prod_unique]
    show gm (y ≫ 𝟙 X) z _ (L.g i (J y)) ^ (n : ℤ) = _
    rw [Category.comp_id]
  have f₄ : trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] y z ![i₀, i] ![J o, J y] =
      gm o z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm y z _ (L.g i (J y)) ^ (-((N : ℤ) ^ 2)) := by
    rw [trF, Fin.prod_univ_two]
    show gm (y ≫ q) z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm (y ≫ 𝟙 X) z _ (L.g i (J y)) ^ (-((N : ℤ) ^ 2)) = _
    rw [hyq, Category.comp_id]
  rw [f₁, f₂, f₃, f₄] at hE'
  rw [val_of w o z J ![J o, J o] (Fin.forall_fin_two.2 ⟨congrArg J hoq, congrArg J (Category.comp_id _)⟩),
    val_of rig b z J (fun _ => J o) (fun _ => congrArg J hbe),
    sval_of s y z J (fun _ => J y) (fun _ => congrArg J (Category.comp_id _)),
    val_of w y z J ![J o, J y] (Fin.forall_fin_two.2 ⟨congrArg J hyq, congrArg J (Category.comp_id _)⟩)]
  exact alg _ _ _ _ _ _ _ N n hE'

end GlobalTheory.CompanionTheory.Ar.Sl.Transl.TorsChart

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem torsVal_charts : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (N : ℕ) (T : F), TorsVal P s y N T → ∀ (z : Sp F) (J : (Sp F ⟶ G.left) → P.L.ι), Good P.L z J → ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen ∧ toStk z T * ((val (Z := Sp F) w (1 : Over.mk b ⟶ G).left z J).val * (val (Z := Sp F) P.rig b z J).val ^ (N ^ 2)) ^ n = sval (Z := Sp F) s y.left z J ^ (N ^ 2) * (val (Z := Sp F) w y.left z J).val ^ n := by
  intro S G _ _ P n s F _ b y N T hT z J hJ
  obtain ⟨-, hy, w, i₀, i, hw, h₀, hi, hE⟩ := hT
  have key : ∀ t : Over.mk b ⟶ G, t ^ N = 1 →
      t.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    intro t ht
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ht]
  have hbe : b ≫ eSec G = (1 : Over.mk b ⟶ G).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl
  refine ⟨w, hw, TorsChart.charts (e := eSec G) hbe (key 1 (one_pow N)) (key y hy) w hw P.rig P.rigGen
    s T i₀ i h₀ hi hE z J hJ⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.OS

section Vals

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hasVal_add {a : K → ℤ} {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y a s z w)
    (h' : Small.HasVal y a s' z w') : Small.HasVal y a (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  obtain ⟨dg', dh', g', f', hg', hf', hd', e', hz0', ez'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := funext fun k => by
    have h1 := hd k
    have h2 := hd' k
    simp only [Pi.add_apply]
    omega
  refine ⟨dg + dh', dh + dh', g * f' + g' * f, f * f',
    FinRd.ValSub.mh_add (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg hf') ?_,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hf hf', fun k => ?_, ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg' hf
  · have h1 := hd k
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_add (f := _), map_mul, e, e']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul, ez, ez']
    ring

theorem hasVal_zsmul {a : K → ℤ} {s : Ω} {w : 𝕜} (n : ℤ) (h : Small.HasVal y a s z w) :
    Small.HasVal y a (n • s) z (n • w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  refine ⟨dg, dh, MvPolynomial.C n * g, f, ?_, hf, hd, ?_, hz0, ?_⟩
  · intro m hm k
    rw [MvPolynomial.C_mul'] at hm
    exact hg m (MvPolynomial.support_smul hm) k
  · rw [map_mul, e, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]
  · rw [map_mul, ez, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]

theorem hasVal_zero_of {a : K → ℤ} {s : Ω} {w : 𝕜} (h : Small.HasVal y a s z w) :
    Small.HasVal y a (0 : Ω) z (0 : 𝕜) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  exact ⟨dg, dh, 0, f, FinRd.ValSub.mh_zero dg, hf, hd, by simp, hz0, by simp⟩

end Vals

section Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

end Coef

section Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end Fin

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end Arch

section ArchD

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

end ArchD

section Emb

end Emb

end GlobalTheory.CompanionTheory.Ar.Rec.OS

namespace GlobalTheory.CompanionTheory.Ar.Rec


end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.chart_lattice_specialization_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (n : ℕ) (ix : Fin n → Fin r), Function.Injective ix → (gramAt h z fun l => B (ix l)).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.coord_degree_bound_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F₀ F₁ : Submodule (𝓞 L) B.carrier), IsSubFibre M (flagStep Ω b₀ i) z MB F₀ →
      IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB F₁ → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∃ φ : F₁ →ₗ[𝓞 L] L, (∀ x, φ x = 0 ↔ (x : B.carrier) ∈ F₀) ∧
        (∀ (x : F₁) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (t : Ω) (u : L),
          e ∈ flagStep Ω b₀ (i + 1) → M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (x : B.carrier)).left) →
          IsCls b₀ i e t → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u → φ x = u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.FinPhi.exists_phi | exact GlobalTheory.CompanionTheory.Ar.RootHt.FinPhi.exists_phi | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.FinPhi.exists_phi <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonObj

theorem exists_val_of_isTan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (v : epsOver T.V T.V ⟶ G.G), IsTan v → ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  intro E _ _ _ H X tX T zV G Ψ hΨ EC _ _ MC v hv
  have hbase : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (epsOver T.V T.V).hom =
      Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [LieTangent.spec_comp, LieTangent.spec_comp]
    congr 2
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hover : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ) ≫ tX.G.hom =
      (epsAt (FinRd.Roots.gen T zV)).hom := by
    have hw : v.left ≫ G.G.hom = (epsOver T.V T.V).hom := Over.w v
    rw [Category.assoc, Category.assoc, hΨ.1.w, ← Category.assoc v.left, hw, ← Category.assoc, hbase,
      Category.assoc]
    rfl
  let vt : epsAt (FinRd.Roots.gen T zV) ⟶ tX.G := Over.homMk _ hover
  have ht : GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G (FinRd.Roots.gen T zV) vt := by
    have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
        (1 : ptOver T.V T.V ⟶ G.G).left := hv
    have h1 := FrameValue.one_left_grp hΨ (Spec.map (CommRingCat.ofHom (algebraMap T.V T.V))) _ rfl
    have hp : Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.V)) ≫ zV = FinRd.Roots.gen T zV := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    have h2 := FrameValue.one_left_pull (G := tX.G) (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) _ _ hp
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.Fr T.Fr T.Fr).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ = _
    rw [← Category.assoc, LieTangent.spec_fst_dual, Category.assoc, ← Category.assoc _ v.left Ψ, hv']
    exact (congrArg (fun u => Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ u) h1).trans h2
  obtain ⟨w, hw⟩ := MC.onto vt ht
  exact ⟨w, congrArg (fun u => u.left) hw⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.root_origin_frame_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ s : CMType H ⊕ CMType H, ∃ σ : 𝓞 E →+* T.V, (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) ∧ ∀ a, algebraMap T.V T.Fr (σ a) = io (labelEmb c s a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.root_origin_frame_nonarchimedean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.root_origin_frame_local_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)), ∃ w : EC, FinRd.Roots.IsFrameVec Or io zT MC w s i ∧ Or.𝔐.M.ValAt (FinRd.Roots.gen T zV) (Or.Fl.b s i) (MC.pt w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.root_origin_generic_frame_final : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → (letI := io.toAlgebra; Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_residue_absolute_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ), 0 < e → 0 < ramOverZ la → (∀ x y : T.Fr, FinRd.absT p la T e (x * y) = FinRd.absT p la T e x * FinRd.absT p la T e y) ∧ FinRd.absT p la T e 1 = 1 ∧ (∀ x : T.Fr, x ≠ 0 → 0 < FinRd.absT p la T e x) ∧ ∀ x : T.Fr, FinRd.absT p la T e x ≤ 1 ↔ x ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts <;> assumption)
end
