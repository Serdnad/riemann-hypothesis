module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle157
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Formalism.LocalToGlobal.Columns.TwQLevU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Dict.Lift

namespace GlobalTheory.Dict.FibreMove

theorem exists_frame_push {X Y : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : LB X}
    {L' : LB Y} (hL : L.IsLB) (hL' : L'.IsLB) {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen)
    (e : V → (Sp ℂ ⟶ Y)) (hol : IsHolTo Set.univ e) (fr : L'.ι → V → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L'.U j})
    (fr_ne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L'.U j ⊓ L'.U j') →
      fr j z = valAt' (e z) (L'.U j ⊓ L'.U j') (L'.g j j').val * fr j' z) :
    ∃ fr' : L.ι → V → ℂ, (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j}) ∧
      (∀ j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j → fr' j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ (L.U j ⊓ L.U j') →
        fr' j z = valAt' (e z ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * fr' j' z) ∧
      ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr' a z = wv w (e z) a j * fr j z := by
  choose ch hch using fun z => exists_chart (e z) L' hL'
  have key : ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j →
      wv w (e z) a (ch z) * fr (ch z) z = wv w (e z) a j * fr j z := by
    intro a j z ha hj
    have h0 := (top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have h2 := valAt'_unit_ne_zero (e z) h0 (L'.g (ch z) j)
    rw [wv_change hw ha ha (hch z) hj, val_g_self _ L hL a ha, fr_g (ch z) j z h0]
    field_simp
  refine ⟨fun a z => wv w (e z) a (ch z) * fr (ch z) z, fun a z₀ hz₀ => ?_, fun a z ha => ?_,
    fun a a' z h => ?_, key⟩
  · have hN := (hol ((L.pull φ).U (fun _ => a) ⊓ L'.U (ch z₀)) (w.s (fun _ => a, ch z₀)).val)
    have hm := hN.1.mem_nhds (x := z₀) ⟨trivial, mem_both hz₀ (hch z₀)⟩
    have hsub : ∀ z, ⊤ ≤ e z ⁻¹ᵁ ((L.pull φ).U (fun _ => a) ⊓ L'.U (ch z₀)) →
        ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a ∧ ⊤ ≤ e z ⁻¹ᵁ L'.U (ch z₀) := fun z hz =>
      ⟨(mem_wchart (e z) L _ _).1 ((top_le_preimage_inf _ _ _).1 hz).1 ⟨⟩, ((top_le_preimage_inf _ _ _).1 hz).2⟩
    have d1 : DifferentiableAt ℂ (fr (ch z₀)) z₀ :=
      (fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hm fun z hz => (hsub z hz.2).2)
    have d2 : DifferentiableAt ℂ (fun z => wv w (e z) a (ch z₀)) z₀ := hN.2.differentiableAt hm
    refine ((d2.mul d1).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact key a (ch z₀) z (hsub z hz.2).1 (hsub z hz.2).2
  · exact mul_ne_zero (wv_ne w ha (hch z)) (fr_ne _ z (hch z))
  · obtain ⟨ha, ha'⟩ := (top_le_preimage_inf _ _ _).1 h
    simp only []
    rw [wv_change hw ha ha' (hch z) (hch z), val_g_self _ L' hL' _ (hch z)]
    ring

theorem anFib_levR {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} {y y' : FrPt Xo c ℂ} (h : levR (gM, gA) y y')
    (A : AnFib X bas idx e x L y) :
    ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧
      ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  obtain ⟨ρ, ν, -, hν, hmv⟩ := h
  obtain ⟨hb, hu, pm, w, hf, hs, hcub, hc⟩ := MoveCalc.frMove_iff_carry.1 hmv
  obtain ⟨hw, hrig, -⟩ := hcub
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv ν.cart y.x y'.x hb.symm
  let ex : (Fin g → ℂ) → (ptO Xo y'.x ⟶ Xo.univ.t.G) := fun z => Φ (A.ex z)
  have hex : ∀ z, (ex z).left = (A.ex z).left ≫ ν.φ := fun z => hΦ _
  obtain ⟨fr, fr_hol, fr_ne, fr_g, key⟩ := exists_frame_push Xo.univ.t.PP.isLB Xo.univ.t.PP.isLB hw
    (fun z => (A.ex z).left) A.hol A.fr A.fr_hol A.fr_ne A.fr_g
  have hch : ∀ z, ∃ j, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j :=
    fun z => exists_chart _ _ Xo.univ.t.PP.isLB
  have hadd : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => by
    simp only [ex, A.ex_add, map_mul]
  have hex0 : (A.ex 0).left = y.x ≫ eSec Xo.univ.t.G := by
    have h0 : A.ex 0 = 1 := by
      have := A.ex_add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [h0]
    exact one_left _
  let A' : AnFib X bas idx e x L y' :=
    { ex := ex
      ex_add := hadd
      ex_onto := Φ.surjective.comp A.ex_onto
      ex_ker := fun z => by
        rw [← A.ex_ker]
        exact Φ.map_eq_one_iff
      ex_lin := fun a z => by
        apply Over.OverMorphism.ext
        rw [hex, A.ex_lin, Over.comp_left, Over.comp_left, Category.assoc, ν.act, ← Category.assoc, hex]
      hol := (funext hex).symm ▸ PullbackSections.isHolTo_comp A.hol ν.φ
      der := fun ℓ => by
        have h1 := FibreDeriv.isDerivAt0_comp (A.der ℓ) ν.φ
        rw [hu]
        exact (funext hex).symm ▸ h1
      fr := fr
      fr_hol := by simpa only [hex] using fr_hol
      fr_ne := by simpa only [hex] using fr_ne
      fr_g := by simpa only [hex] using fr_g
      fr_0 := fun a ha => by
        rw [hex] at ha
        obtain ⟨j, hj⟩ := hch 0
        have h1 := key a j 0 ha hj
        have h2 := A.fr_0 j hj
        have h3 := val_rig ν.cm Xo.univ.t.PP Xo.univ.t.PP w hrig y.x a j (hex0 ▸ ha) (hex0 ▸ hj)
        have h4 : y.x ≫ ν.cm.e = y'.x := by rw [ν.base]; exact hb.symm
        erw [h4, ← h2, ← hex0] at h3
        exact h1.trans h3.symm
      χ := A.χ
      χ_norm := A.χ_norm
      fr_per := fun v hv a z ha => by
        rw [hex] at ha
        obtain ⟨j, hj⟩ := hch z
        have hz : A.ex (z + pv X idx x v) = A.ex z := by
          rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
        have h1 := key a j z ha hj
        have h2 := key a j (z + pv X idx x v) (hz ▸ ha) (hz ▸ hj)
        have h3 := A.fr_per v hv j z hj
        simp only [hz] at h2
        rw [h1, h2, h3]
        ring }
  refine ⟨A', fun θ hθ a z pt' hp1 hp2 ha => ?_, fun mk hmk a ha => ?_⟩
  · obtain ⟨j, hj⟩ := hch z
    have ha' : ⊤ ≤ ((A.ex z).left ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U a := hex z ▸ ha
    let pt : Sp ℂ ⟶ Gx y.x := pullback.lift (𝟙 _) (A.ex z).left (by
      rw [Category.id_comp]; exact (Over.w (A.ex z)).symm)
    have e₁ : pt ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (A.ex z).left := pullback.lift_snd _ _ _
    have e₂ : pt ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = 𝟙 _ := pullback.lift_fst _ _ _
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact hp2.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · refine (hp1.trans (hex z)).trans ?_
        rw [← e₁]
        exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm
    have h1 := hθ j z pt e₁ e₂ hj
    have h2 := MoveValues.val_carry hs hc pt (i := a) (j := j)
      (by rw [e₁]; exact (MoveValues.mem_iff ((A.ex z).left ≫ ν.φ) _).2 ha')
      (by rw [e₁]; exact (MoveValues.mem_iff _ _).2 hj)
    refine h2.trans ?_
    rw [e₁]
    refine (congrArg (wv w (A.ex z).left a j * ·) h1).trans ?_
    change _ = θ z * fr a z ^ (1 : ℤ)
    rw [zpow_one, zpow_one, key a j z ha' hj]
    ring
  · have ha' : gM a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := gM) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    change _ = Φ (A.ex (pv X idx x ((l.M : E)⁻¹ • mk (gM a))))
    rw [← hmk _ ha']
    apply Over.OverMorphism.ext
    rw [hΦ, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, hν.2.1, toUnit_left, toUnit_left, hb]
    exact Category.assoc _ _ _

end GlobalTheory.Dict.FibreMove

theorem GlobalTheory.Dict.FibreMove.anFib_levR_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (gM : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c ℂ), levR (gM, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La)) y y' → ∀ A : AnFib X bas idx e x L y, ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h A => GlobalTheory.Dict.FibreMove.anFib_levR h A
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7}

def word (θ : InfF D) (V : HSp D) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) :
    GA D V → ℂ := l.foldr (fun p f => Rder θ V p.1 p.2 f) φ

def IsMod (θ : InfF D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  φ ∈ SmFun θ V ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    Continuous (word θ V l φ) ∧ ∃ (N : ℕ) (C : ℝ), ∀ g, ‖word θ V l φ g‖ ≤ C * (height θ V g : ℝ) ^ N

private theorem word_mem_smFun {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : word θ V l φ ∈ SmFun θ V := by
  induction l with
  | nil => exact hφ
  | cons p l ih =>
    exact Rder_mem (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)) (hl p (by simp))

theorem word_add {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {φ ψ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hψ : ψ ∈ SmFun θ V) :
    word θ V l (φ + ψ) = word θ V l φ + word θ V l ψ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    show Rder θ V p.1 p.2 (word θ V l (φ + ψ)) =
      Rder θ V p.1 p.2 (word θ V l φ) + Rder θ V p.1 p.2 (word θ V l ψ)
    rw [ih hl', Rder_add (word_mem_smFun hl' hφ) (word_mem_smFun hl' hψ) (hl p (by simp))]

theorem word_smul {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (c : ℂ) (φ : GA D V → ℂ) : word θ V l (c • φ) = c • word θ V l φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    show Rder θ V p.1 p.2 (word θ V l (c • φ)) = c • Rder θ V p.1 p.2 (word θ V l φ)
    rw [ih fun q hq => hl q (List.mem_cons_of_mem _ hq), Rder_smul]

theorem word_Rder {θ : InfF D} {V : HSp D} (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    word θ V l (Rder θ V τ X φ) = word θ V (l ++ [(τ, X)]) φ := by
  unfold word
  rw [List.foldr_append]
  rfl

def Decay (θ : InfF D) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | φ ∈ SmFun θ V ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    Continuous (word θ V l φ) ∧ IsRapidDecay θ V (word θ V l φ)}
  add_mem' := by
    rintro φ ψ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨add_mem a1 b1, fun γ hγ g => by simp only [Pi.add_apply, a2 γ hγ, b2 γ hγ], fun l hl => ?_⟩
    rw [word_add hl a1 b1]
    refine ⟨(a3 l hl).1.add (b3 l hl).1, fun N => ?_⟩
    obtain ⟨C, hC⟩ := (a3 l hl).2 N
    obtain ⟨C', hC'⟩ := (b3 l hl).2 N
    refine ⟨C + C', fun g => le_trans ?_ (add_le_add (hC g) (hC' g))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  zero_mem' := by
    refine ⟨zero_mem _, fun _ _ _ => rfl, fun l hl => ?_⟩
    have := word_smul (θ := θ) hl 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact ⟨continuous_const, fun N => ⟨0, fun g => by simp⟩⟩
  smul_mem' := by
    rintro c φ ⟨a1, a2, a3⟩
    refine ⟨Submodule.smul_mem _ c a1, fun γ hγ g => by simp only [Pi.smul_apply, a2 γ hγ], fun l hl => ?_⟩
    rw [word_smul hl]
    refine ⟨(a3 l hl).1.const_smul c, fun N => ?_⟩
    obtain ⟨C, hC⟩ := (a3 l hl).2 N
    refine ⟨‖c‖ * C, fun g => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c)

theorem Rder_left {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} {γ : GA D V} (h : ∀ g, φ (γ * g) = φ g)
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) :
    Rder θ V τ X φ (γ * g) = Rder θ V τ X φ g := by
  show deriv (fun t : ℝ => φ (γ * g * oneP θ V τ X t)) 0 = deriv (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simp only [mul_assoc, h]

theorem append_mem_lie {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    ∀ p ∈ l ++ [(τ, X)], p.2 ∈ lieAt V p.1 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hl p hp
  · rw [List.mem_singleton] at hp
    subst hp
    exact hX

theorem Rder_mem_Decay {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} (h : φ ∈ Decay θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ Decay θ V := by
  obtain ⟨h1, h2, h3⟩ := h
  refine (show _ ∧ _ ∧ _ from ⟨Rder_mem h1 hX, fun γ hγ g => Rder_left (h2 γ hγ) τ X g, fun l hl => ?_⟩)
  rw [word_Rder]
  exact h3 _ (append_mem_lie hl hX)

theorem IsMod.rder {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} (h : IsMod θ V φ) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : IsMod θ V (Rder θ V τ X φ) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold IsMod
  refine ⟨Rder_mem h1 hX, fun γ hγ g => Rder_left (h2 γ hγ) τ X g, fun l hl => ?_⟩
  rw [word_Rder]
  exact h3 _ (append_mem_lie hl hX)

private theorem word_const_eq_const_norm_le {θ : InfF D} {V : HSp D} (c : ℂ)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    ∃ d : ℂ, word θ V l (fun _ => c) = (fun _ => d) ∧ ‖d‖ ≤ ‖c‖ := by
  induction l with
  | nil => exact ⟨c, rfl, le_rfl⟩
  | cons p l ih =>
    obtain ⟨d, hd, -⟩ := ih
    refine ⟨0, ?_, by simp⟩
    show Rder θ V p.1 p.2 (word θ V l fun _ => c) = _
    rw [hd]
    funext g
    simp [Rder]

theorem isMod_const (θ : InfF D) (V : HSp D) (c : ℂ) : IsMod θ V fun _ => c := by
  unfold IsMod
  refine ⟨?_, fun _ _ _ => rfl, fun l _ => ?_⟩
  · intro k τs Xs _ g
    exact contDiff_const
  · obtain ⟨d, hd, hdc⟩ := word_const_eq_const_norm_le (θ := θ) (V := V) c l
    rw [hd]
    exact ⟨continuous_const, 0, ‖c‖, fun _ => by rw [pow_zero, mul_one]; exact hdc⟩

structure IsKerSys (θ : InfF D) (V W : HSp D) {M : Type} [AddCommGroup M] [Module ℂ M]
    (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)) : Prop where
  cont : ∀ f, Continuous fun p : GA D V × GA D W => κ f p.1 p.2
  left : ∀ f, ∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, κ f (γ * g) (δ * h) = κ f g h
  level : ∀ f, ∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧
    IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, κ f (g * k) (h * k') = κ f g h
  growth : ∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ g h, ‖κ f g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N
  derV : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f, ∃ f', ∀ g h,
    HasDerivAt (fun t : ℝ => κ f (g * oneP θ V τ X t) h) (κ f' g h) 0
  derW : ∀ τ, ∀ X ∈ lieAt W τ, ∀ f, ∃ f', ∀ g h,
    HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0
  cap : ∀ τ, ∃ a b : ℕ → Module.End ℂ M, (∀ k f h, gelf θ V τ k (fun g => κ f g h) = fun g => κ (a k f) g h) ∧
    (∀ k f g, gelf θ W τ k (κ f g) = κ (b k f) g) ∧ Algebra.adjoin ℂ (Set.range a) = Algebra.adjoin ℂ (Set.range b)

def swapKer {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)) :
    M →ₗ[ℂ] (GA D W → GA D V → ℂ) where
  toFun f h g := κ f g h
  map_add' f f' := by rw [map_add (f := _)]; rfl
  map_smul' c f := by rw [map_smul]; rfl

theorem IsKerSys.swap {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (h : IsKerSys θ V W κ) : IsKerSys θ W V (swapKer κ) := by
  refine ⟨fun f => (h.cont f).comp continuous_swap, fun f γ hγ δ hδ g g' =>
    h.left f δ hδ γ hγ g' g, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨U, U', hU, hU', hk⟩ := h.level f
    exact ⟨U', U, hU', hU, fun k hk1 hk2 k' hk1' hk2' g g' => hk k' hk1' hk2' k hk1 hk2 g' g⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun f => ?_⟩
    obtain ⟨C, hC⟩ := hN f
    refine ⟨C, fun g g' => ?_⟩
    have hb := hC g' g
    rw [mul_comm (height θ V g' : ℝ)] at hb
    exact hb
  · intro τ X hX f
    obtain ⟨f', hf'⟩ := h.derW τ X hX f
    exact ⟨f', fun g g' => hf' g' g⟩
  · intro τ X hX f
    obtain ⟨f', hf'⟩ := h.derV τ X hX f
    exact ⟨f', fun g g' => hf' g' g⟩
  · intro τ
    obtain ⟨a, b, ha, hb, hab⟩ := h.cap τ
    exact ⟨b, a, fun k f g' => hb k f g', fun k f g => ha k f g, hab.symm⟩

def OmCont (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w

def thKer (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GlobalTheory.RealWeil.thetaSub ψ S T →ₗ[ℂ] (GA D S → GA D T → ℂ) where
  toFun f g h := om (g, h) f.1 0
  map_add' f f' := by funext g h; simp
  map_smul' c f := by funext g h; simp

end GlobalTheory.Mem.Lift

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.TopCh

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

theorem phi_int (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) ≤ 1 := by

  have h : Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) =
      P.valuation E (algebraMap (𝓞 E) E r) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := P) _
  rw [h]
  exact HeightOneSpectrum.valuation_le_one (K := E) (v := P) r

theorem phi_lt (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal := by
  have h : Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) =
      P.valuation E (algebraMap (𝓞 E) E r) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := P) _
  rw [h]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) (v := P) r

def locLev (P : HeightOneSpectrum (𝓞 E)) (Θ : LevI E K n P) (d : E) : Subgroup (GL (Fin n) (P.adicCompletion E)) :=
  qbU (F := E) P (algebraMap E (P.adicCompletion E)) (phi_int P) (phi_lt P) Θ (algebraMap E (P.adicCompletion E) d)

abbrev iotaP (P : HeightOneSpectrum (𝓞 E)) : ↥(GLint E n P) →* GL (Fin n) (P.adicCompletion E) :=
  qbIota (F := E) P (algebraMap E (P.adicCompletion E))

def locChr (P : HeightOneSpectrum (𝓞 E)) (Θ : LevI E K n P) (d : E) (hd : d ≠ 0) {N : ℕ} (hdN : P.valuation E d ≤ WithZero.exp (-(N : ℤ)))
    (hΘ : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ Θ.H, Θ.lam ⟨g, h⟩ = 1) : locLev P Θ d →* Kˣ :=
  qbChr (F := E) P (algebraMap E (P.adicCompletion E)) (phi_int P) (phi_lt P) Θ d hd hdN hΘ

end Loc

section Ad

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] {n : ℕ}
  {Q : Finset (HeightOneSpectrum (𝓞 E))}


variable (F) in
abbrev rhoP (P : HeightOneSpectrum (𝓞 E)) : GL (Fin n) (AfE F E) →* GL (Fin n) (P.adicCompletion E) := bc (adAt F P)


variable (F) in
def rhoT (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) : GL (Fin n) (AfE F E) →* GL (Fin n) (P.adicCompletion E) :=
  (rhoP F P).comp (MulAut.conj t⁻¹).toMonoidHom

def topU (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) : Subgroup (GL (Fin n) (AfE F E)) :=
  U ⊓ ⨅ P : Q, (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)

theorem topU_le (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) : topU U t Θ d ≤ U :=
  inf_le_left

theorem rhoT_mem {U : Subgroup (GL (Fin n) (AfE F E))} {t : GL (Fin n) (AfE F E)} {Θ : LevQFam E K n Q} {d : Q → E}
    {x : GL (Fin n) (AfE F E)} (hx : x ∈ topU U t Θ d) (P : Q) : rhoT F P.1 t x ∈ locLev P.1 (Θ P) (d P) := by
  have hx' : x ∈ U ⊓ ⨅ P : Q, (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t) := hx
  exact Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hx').2 P)

def topChi (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0)
    (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) :
    topU U t Θ d →* ℂˣ :=
  (∏ P : Q, (Units.map (σ : K →* ℂ)).comp ((locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P)).comp
    (((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ fun x => rhoT_mem x.2 P)))⁻¹

end Ad

instance neZero_top (R : Ranks) : NeZero (R.N R.m) := ⟨by have := N_m_succ R; omega⟩

end GlobalTheory.Mem.Col2.TopCh

end
end
