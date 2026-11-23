module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle053
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomRangeSubset
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle061
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle062
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

section
variable {S : Scheme.{0}}

theorem exists_gtDatum_of_units (E : SplitExt S) {G : Over S} [GrpObj G] (q : G ⟶ E.B) (i : splitTorus S E.X ⟶ G)
    (hq : IsMonHom q) (hi : IsMonHom i) (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q (η[E.B]))
    (s : ∀ (χ : E.X) (a : (E.O χ).L.ι), Γ(G.left, q.left ⁻¹ᵁ (E.O χ).L.U a)ˣ)
    (h₁ : ∀ (χ : E.X) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (a a' : (E.O χ).L.ι), q.left (r z) ∈ (E.O χ).L.U a →
      q.left (r z) ∈ (E.O χ).L.U a' →
      gm r z _ (s χ a') = gm (r ≫ q.left) z _ ((E.O χ).L.g a a') * gm r z _ (s χ a))
    (h₂ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (Z : Over S) (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (g.left z) ∈ (E.O χ).L.U a →
      gm ((t ≫ i) * g).left z _ (s χ a) = gm t.left z ⊤ (charUnit S E.X χ) * gm g.left z _ (s χ a))
    (h₃ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (y : (𝟙_ (Over S)).left), q.left (eSec G y) ∈ (E.O χ).L.U a →
      gm (eSec G) y _ (s χ a) * gm (𝟙 _) y _ ((E.O χ).rig.s fun _ => a) = 1) :
    ∃ d : E.GtDatum G, d.q = q ∧ d.i = i := by
  have hact : ∀ {Z : Over S} (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (((t ≫ i) * g).left z) = q.left (g.left z) := by
    intro Z t g z
    have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
      rw [MonObj.mul_comp, Category.assoc, hk.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
    exact congrArg (fun f => f.left z) e
  let u : ∀ (j : E.ChartIdx) (_k : Module.Free.ChooseBasisIndex ℤ E.X), Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ :=
    fun j k => res (Scheme.Hom.preimage_mono q.left (E.chart_le j k)) (s _ (j k))
  have hu : ∀ (j : E.ChartIdx) k {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ E.chart j →
      gm r z (q.left ⁻¹ᵁ E.chart j) (u j k) = gm r z _ (s _ (j k)) := fun j k Z r z hz => gm_res r z _ hz _
  refine ⟨{
    q := q, i := i, q_hom := hq, i_hom := hi, q_flat := hf, q_surjective := hs, q_affine := ha, isKernel := hk
    u := u
    coord := fun j V hV h => ?_
    trans := fun j j' k => unit_ext fun y hy => ?_
    act_le := fun j y hy => (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    equiv := fun j k => unit_ext fun y hy => ?_
    unit_norm := fun j k => unit_ext fun y hy => ?_ }, rfl, rfl⟩
  · refine bijective_of_basis E.basis q i hq hi hf hs ha hk V hV _ fun k Z t g z hz => ?_
    have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rw [hact]; exact hz
    rw [gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz', gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz, hu j k _ z (h hz'), hu j k _ z (h hz)]
    exact h₂ _ _ Z t g z (E.chart_le j k (h hz))
  · refine ((gm_res _ y _ hy _).trans ((hu j' k _ y hy.2).trans
      (h₁ _ _ (𝟙 _) y (j k) (j' k) (E.chart_le j k hy.1) (E.chart_le j' k hy.2)))).trans (Eq.symm ?_)
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull (𝟙 _) q.left y (E.chart j ⊓ E.chart j') hy _).trans
      (gm_res _ y (V := E.chart j ⊓ E.chart j') _ hy _)) ((gm_res _ y _ hy _).trans (hu j k _ y hy.1)))
  · have hy' : q.left (((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y) ∈ E.chart j :=
      (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    have e := h₂ _ (j k) _ (fst _ _) (snd _ _) y (E.chart_le j k hy)
    rw [← hu j k _ y hy, ← hu j k _ y hy'] at e
    refine ((gm_res _ y _ hy _).trans ((gm_pull (𝟙 _) ((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y
      (q.left ⁻¹ᵁ E.chart j) hy' _).trans ?_)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res (𝟙 _) y _ hy _).trans
        (gm_pull (𝟙 _) (fst (splitTorus S E.X) G).left y ⊤ trivial _))
        (gm_pull (𝟙 _) (snd (splitTorus S E.X) G).left y (q.left ⁻¹ᵁ E.chart j) hy _))).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
    exact e
  · refine Eq.trans ?_ ((h₃ _ (j k) y (E.chart_le j k hy.1)).trans (map_one _).symm)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hy _).trans
      ((gm_pull (𝟙 _) (eSec G) y (q.left ⁻¹ᵁ E.chart j) hy.1 _).trans ?_)) (gm_res _ y _ hy _))
    rw [Category.id_comp]
    exact hu j k _ y hy.1

end

theorem exists_gtDatum_of_gtCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G), ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (xe : E.X ≃+ D.X) (d : E.GtDatum (thickObj R I e G)) (π : E.B.left ⟶ D.P.A.left), IsGrpPullback E.B D.P.A (thick R I e) π ∧ d.q.left ≫ π = g.pG.left ∧ (∀ χ, LBIso (E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) ∧ ∀ χ, UFib.GenWt (G := thickObj R I e G) d.i (g.t (xe χ)) χ := by
  intro R _ _ I D e G _ _ g
  have := g.q_hom
  have he : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (fun f => f.left) (IsMonHom.one_hom g.q)
  choose ρ hρ hρ' using fun χ => exists_rig g.q.left _ _ he (bundle I D e χ) (coordUnit g χ) (coordUnit_trans g χ)
  let E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    { B := thickObj R I e D.P.A
      isAbelian := isAbelianScheme_thick I D e
      X := D.X
      O := fun χ => ⟨bundle I D e χ, ρ χ, DVR.linComb_isLB _ D.P.isLB _ _, hρ χ⟩
      addIso := bundle_add I D e
      zeroTriv := bundle_zero I D e
      primitive := bundle_primitive I D e }
  obtain ⟨d, hq, hi⟩ := exists_gtDatum_of_units E g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj g.q_affine g.isKernel
    (coordUnit g) (coordUnit_trans g) (coordUnit_weight g) hρ'
  refine ⟨E, AddEquiv.refl _, d, (D.prBe I e).left, isGrpPullback_pullback D.P.A (thick R I e), ?_, fun χ => ?_,
    fun χ => ?_⟩
  · rw [hq]
    rfl
  · refine exists_iso D.P.isLB (funext fun k => ?_) Oε
    refine Eq.trans ?_ (WeightPf.Oφ_comp (D.prBe I e) (𝟙 _) χ k).symm
    rw [Category.comp_id]
  · rw [hi]
    intro Z t y z J hJ
    have v := TorusCoord.val_t_act g t y χ (𝟙 _) z J hJ
    have c : splitTorusPointsEquiv _ D.X Z t (Multiplicative.ofAdd χ) = pullU t.left ⊤ (charUnit _ D.X χ) :=
      Units.ext (splitTorusPointsEquiv_val _ _ _ t χ)
    have c' := gm_pull (𝟙 _) t.left z ⊤ trivial (charUnit _ D.X χ)
    rw [Category.id_comp] at c'
    rw [Category.id_comp, Category.id_comp, c] at v
    exact v.trans (congrArg (· * _) c')

end GlobalTheory.ZH.UFib
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_isPullback_of_projChart' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart | exact GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart | (intros; apply GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

theorem norm_const_gen : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (nH : H ⟶ H) (nK : HK ⟶ HK) (nX : X ⟶ X), nK ≫ j = j ≫ nH → nK ≫ ψ = ψ ≫ nX → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1])), α.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l l' : M.ι) (m : Fin 2 → L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (c ≫ nH) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) → ⊤ ≤ (x ≫ ψ ≫ nX) ⁻¹ᵁ L.U (m 1) → ‖valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x l (m 0) ^ n ^ 2 * (ω (x ≫ nK) l' (m 1))⁻¹‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω nH nK nX hnj hnψ n α hα
  have ej : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ j = (x ≫ j) ≫ nH := fun x => by
    rw [Category.assoc, hnj, Category.assoc]
  have eψ : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ ψ = (x ≫ ψ) ≫ nX := fun x => by
    rw [Category.assoc, hnψ, Category.assoc]
  have w₀ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ L.U (m 0) := fun m => LB.wchart_le L ![𝟙 X, nX] m 0
  have w₁ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ nX ⁻¹ᵁ L.U (m 1) := fun m => LB.wchart_le L ![𝟙 X, nX] m 1
  have l₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {a : M.ι × M.ι}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) →
      ⊤ ≤ ((x ≫ nK) ≫ j) ⁻¹ᵁ M.U a.2 := fun h => by
    rw [ej]
    exact fun _ hz => (h hz).2
  have m₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {m}, ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m →
      ⊤ ≤ ((x ≫ nK) ≫ ψ) ⁻¹ᵁ L.U (m 1) := fun h => by
    rw [eψ]
    exact fun _ hz => w₁ _ (h hz)
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (M.ι × M.ι) (Fin 2 → L.ι)
    (fun a => M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) (fun m => ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m)
    (fun a m x => valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x a.1 (m 0) ^ n ^ 2 *
      (ω (x ≫ nK) a.2 (m 1))⁻¹)
    (fun z => exists_chart (LB.isLB_linComb hL ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1]) (ψ z))
    (fun a m => ((Reg.pull ψ inf_le_right _).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) ⊓ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m) a.1 (m 0)
        (fun _ hz => hz.1.1) fun _ hz => w₀ _ hz.2).1).pow _)).mul
      (hω.reg nK _ a.2 (m 1) (by rw [hnj]; exact fun _ hz => hz.1.2) (by rw [hnψ]; exact fun _ hz => w₁ _ hz.2)).2)
    (fun a m x _ ha hm => mul_ne_zero (mul_ne_zero (val_unit_ne_zero (x ≫ ψ) (U := LB.wchart L ![𝟙 X, nX] m) hm _)
      (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => (ha hz).1) fun _ hz => w₀ _ (hm hz))))
      (inv_ne_zero (hω.ne _ _ _ (l₁ ha) (m₁ hm))))
    (fun a m m' x _ ha hm hm' => by
      have hm₀ : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) := fun _ hz => w₀ _ (hm hz)
      have hm₀' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m' 0) := fun _ hz => w₀ _ (hm' hz)
      have e := (gen_val hα (x := x ≫ ψ) hm hm').trans (congrArg (· * _) (tv_linComb L _ _
        (fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m k (hm hz)) fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m' k (hm' hz)))
      rw [Fin.prod_univ_two] at e
      change valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val =
        tv L ((x ≫ ψ) ≫ 𝟙 X) (m 0) (m' 0) ^ ((n : ℤ) ^ 2) * tv L ((x ≫ ψ) ≫ nX) (m 1) (m' 1) ^ (-1 : ℤ) *
        valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m') (α.s m').val at e
      rw [Category.comp_id, ← eψ, zpow_neg_one,
        show ∀ z : PadicAlgCl p, z ^ ((n : ℤ) ^ 2) = z ^ n ^ 2 from fun z => by rw [← zpow_natCast, Nat.cast_pow]] at e
      beta_reduce
      rw [e, ← hω.right x a.1 (m 0) (m' 0) (fun _ hz => (ha hz).1) hm₀ hm₀',
        ← hω.right (x ≫ nK) a.2 (m 1) (m' 1) (l₁ ha) (m₁ hm) (m₁ hm'), mul_pow, mul_inv]
      ring)
    (fun a a' => by
      have e₁ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ M.U a.1 ⊓ M.U a'.1 :=
        inf_le_inf inf_le_left inf_le_left
      have e₂ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ nH ⁻¹ᵁ (M.U a.2 ⊓ M.U a'.2) :=
        fun _ hz => ⟨hz.1.2, hz.2.2⟩
      refine ⟨res e₁ (M.g a.1 a'.1) ^ ((n ^ 2 : ℕ) : ℤ) * res e₂ (pullU nH _ (M.g a.2 a'.2)) ^ (-1 : ℤ),
        fun m x _ ha ha' hm => ?_⟩
      have hh : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2)) :=
        fun _ hz => ⟨ha hz, ha' hz⟩
      have v₁ : valR (x ≫ j) _ (res e₁ (M.g a.1 a'.1)).val = tv M (x ≫ j) a.1 a'.1 := valR_res _ e₁ hh _
      have v₂ : valR (x ≫ j) _ (res e₂ (pullU nH _ (M.g a.2 a'.2))).val = tv M ((x ≫ nK) ≫ j) a.2 a'.2 := by
        rw [ej]
        exact val_res_pull _ nH e₂ hh _
      beta_reduce
      rw [Units.val_mul, valR_mul _ _ hh, val_zpow _ hh, val_zpow _ hh, v₁, v₂, zpow_natCast, zpow_neg_one,
        hω.left x a.1 a'.1 (m 0) (fun _ hz => (ha hz).1) (fun _ hz => (ha' hz).1) fun _ hz => w₀ _ (hm hz),
        hω.left (x ≫ nK) a.2 a'.2 (m 1) (l₁ ha) (l₁ ha') (m₁ hm), mul_pow, mul_inv]
      ring)
  refine ⟨κ, hκ, fun c x l l' m hc hx hq hl hl' hm hm' => h (l, l') m c x hc hx hq (fun _ hz => ⟨hl hz, hl' hz⟩)
    fun _ hz => Set.mem_iInter.2 fun k => ?_⟩
  fin_cases k
  · exact hm hz
  · exact hm' hz

theorem norm_const_sec : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (Y : Scheme.{0}) (π : Y ⟶ X) (ψ' : HK ⟶ Y), ψ' ≫ π = ψ → ∀ (N : ℕ) (J : Type) [Fintype J] (s : J → (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (N : ℤ))).Sec) (t : J → (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 H) (fun _ => (N : ℤ))).Sec) (b : Matrix J J K), (∀ (x : Sp (PadicAlgCl p) ⟶ HK) v, x ≫ q = spMap σ → Crd _ s (x ≫ ψ') v → Crd _ t (x ≫ j) ((b.map σ).mulVec v)) → (∀ (c : Sp (OO p) ⟶ H) w, c ≫ f = spMap jV → Crd _ t c w → ∃ i, IsUnit (w i)) → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l : M.ι) (m : L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → IsGreatest (Set.range fun i => ‖(b.map σ).mulVec (fun i => valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) (fun _ => m)) ((s i).f fun _ => m)) i * ω x l m ^ N‖) κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω Y π ψ' hψ N J _ s t b hlink hprim
  subst hψ
  let v : (Sp (PadicAlgCl p) ⟶ HK) → L.ι → J → PadicAlgCl p := fun x m i =>
    valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) fun _ => m) ((s i).f fun _ => m)
  let w : (Sp (PadicAlgCl p) ⟶ H) → M.ι → J → PadicAlgCl p := fun x l i =>
    valR x (LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l) ((t i).f fun _ => l)
  have wl : ∀ l i, H.basicOpen ((t i).f fun _ => l) ≤ M.U l := fun l i =>
    (H.basicOpen_le _).trans (LB.wchart_le M (fun _ : Fin 1 => 𝟙 H) (fun _ => l) 0)
  have wne : ∀ {x : Sp (PadicAlgCl p) ⟶ H} {l i}, ⊤ ≤ x ⁻¹ᵁ H.basicOpen ((t i).f fun _ => l) → w x l i ≠ 0 :=
    fun h => ((isUnit_valR_iff _ _ (fun _ hz => H.basicOpen_le _ (h hz)) _).2 h).ne_zero
  have hv : ∀ x m m', ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m' → ∀ i,
      (b.map σ).mulVec (v x m) i = tv L (x ≫ ψ' ≫ π) m m' ^ N * (b.map σ).mulVec (v x m') i := by
    intro x m m' hm hm' i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e := (sec_val (s k) (x := x ≫ ψ') (i := fun _ => m) (j := fun _ => m') (le_wchart fun _ => hm)
      (le_wchart fun _ => hm')).trans (congrArg (· * _) (tv_linComb L _ _ (fun _ => hm) fun _ => hm'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.assoc] at e
    rw [mul_left_comm]
    exact congrArg _ e
  have hw : ∀ x l l', ⊤ ≤ x ⁻¹ᵁ M.U l → ⊤ ≤ x ⁻¹ᵁ M.U l' → ∀ i, w x l i = tv M x l l' ^ N * w x l' i := by
    intro x l l' hl hl' i
    have e := (sec_val (t i) (x := x) (i := fun _ => l) (j := fun _ => l') (le_wchart fun _ => hl)
      (le_wchart fun _ => hl')).trans (congrArg (· * _) (tv_linComb M _ _ (fun _ => hl) fun _ => hl'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.comp_id] at e
    exact e
  have key : ∀ x l m, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m →
      ∃ c : PadicAlgCl p, c ≠ 0 ∧ ∀ i, (b.map σ).mulVec (v x m) i = c * w (x ≫ j) l i := by
    intro x l m hx hl hm
    have h₁ := hlink x (v x m) hx ⟨fun _ => m, 1, le_wchart fun _ => hm, fun i => (_root_.one_mul _).symm⟩
    obtain ⟨c, hc⟩ := crd_unique (s := t) (x := x ≫ j) (v := w (x ≫ j) l)
      ⟨fun _ => l, 1, fun _ hz => Set.mem_iInter.2 fun _ => hl hz, fun i => (_root_.one_mul _).symm⟩ h₁
    exact ⟨c, c.ne_zero, hc⟩
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (J × M.ι) L.ι
    (fun a => H.basicOpen ((t a.1).f fun _ => a.2)) (fun m => (ψ' ≫ π) ⁻¹ᵁ L.U m)
    (fun a m x => (b.map σ).mulVec (v x m) a.1 * ω x a.2 m ^ N * (w (x ≫ j) a.2 a.1)⁻¹)
    (fun z => exists_chart hL _)
    (fun a m => ((Reg.sum fun k => (Reg.const (b a.1 k)).mul (Reg.pull ψ' (U := LB.wchart L (fun _ : Fin 1 => π) fun _ => m)
        (W := j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m)
        (fun _ hz => Set.mem_iInter.2 fun _ => hz.2) ((s k).f fun _ => m))).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m) a.2 m (fun _ hz => wl _ _ hz.1) fun _ hz => hz.2).1).pow _)).mul
      (Reg.inv_basicOpen j _ inf_le_left))
    (fun a m x hx ha hm => by
      obtain ⟨c, hc, e⟩ := key x a.2 m hx (fun _ hz => wl _ _ (ha hz)) hm
      exact mul_ne_zero (mul_ne_zero ((e _).trans_ne (mul_ne_zero hc (wne ha)))
        (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => wl _ _ (ha hz)) hm))) (inv_ne_zero (wne ha)))
    (fun a m m' x _ ha hm hm' => by
      beta_reduce
      rw [hv x m m' hm hm', ← hω.right x a.2 m m' (fun _ hz => wl _ _ (ha hz)) hm hm', mul_pow]
      ring)
    (fun a a' => ⟨1, fun m x hx ha ha' hm => by
      have hl : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a.2 := fun _ hz => wl _ _ (ha hz)
      have hl' : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a'.2 := fun _ hz => wl _ _ (ha' hz)
      obtain ⟨c, -, e⟩ := key x a.2 m hx hl hm
      have h₁ := wne ha
      have h₂ := wne ha'
      beta_reduce
      rw [valR_eq (x ≫ j) (H.basicOpen ((t a.1).f fun _ => a.2) ⊓ H.basicOpen ((t a'.1).f fun _ => a'.2))
        (le_inf ha ha'), Units.val_one, map_one, e, e,
        hw _ a.2 a'.2 hl hl' a'.1, hω.left x a.2 a'.2 m hl hl' hm, mul_pow]
      field_simp⟩)
  refine ⟨κ, hκ, fun c x l m hc hx hq hl hm => ?_⟩
  have hlw : ⊤ ≤ c ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l := fun _ hz => Set.mem_iInter.2 fun _ => hl hz
  obtain ⟨i₀, hi₀⟩ := hprim c _ hc ⟨fun _ => l, 1, hlw, fun i => (_root_.one_mul _).symm⟩
  have hwc : ∀ i, w (x ≫ j) l i = (valR c _ ((t i).f fun _ => l) : OO p) := fun i => by
    rw [hx]
    exact (valR_spMap (OO p).subtype c _ hlw).2 _
  have hle : ∀ i, ‖w (x ≫ j) l i‖ ≤ 1 := fun i => by
    rw [hwc]
    exact (mem_OO_iff _).1 (Subtype.prop _)
  have h1 : ‖w (x ≫ j) l i₀‖ = 1 := by
    obtain ⟨d, hd⟩ := hi₀.exists_right_inv
    have e : w (x ≫ j) l i₀ * (d : PadicAlgCl p) = 1 := by
      rw [hwc]
      exact congrArg Subtype.val hd
    have e' := congrArg norm e
    rw [norm_mul, norm_one] at e'
    exact le_antisymm (hle _) (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  obtain ⟨d, -, e⟩ := key x l m hq (by rw [hx]; exact fun _ _ => hl trivial) hm
  have h₀ := h (i₀, l) m c x hc hx hq ((isUnit_valR_iff _ _ hlw _).1 hi₀) hm
  have hd : ∀ i, ‖(b.map σ).mulVec (v x m) i * ω x l m ^ N‖ = κ * ‖w (x ≫ j) l i‖ := fun i => by
    rw [← h₀]
    simp only [e, norm_mul, norm_inv, h1]
    ring
  refine ⟨⟨i₀, (hd i₀).trans (by rw [h1, _root_.mul_one])⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (hd i).trans_le (mul_le_of_le_one_right hκ.le (hle i))

end GlobalTheory.ZH.FrameNorm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem charts_of_universal {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) {s : J → Ω'}
    (hs : Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤) {I K : Type} [Fintype I] [Fintype K]
    {t : I → Ω} {e : ℕ} {v : K → J → Ω} (ht : M.HasDiv t)
    (hv : ∀ z i, M.Div t i z → EE.E z = Submodule.span (M.O z) (Set.range fun k j => v k j / t i ^ e))
    {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) (hd : M'.HasDiv fun k => pairing φ s (v k))
    (hu : ∀ N : RatModel o Ω', N.HasDiv (fun q : I × K => φ (t q.1) * pairing φ s (v q.2)) →
      ∃ g, M'.IsHom N (AlgHom.id o Ω') g)
    (W : M.Z.Opens) (B : J → J → Ω) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty)
    (hB : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) :
    (∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z') ∧ ∀ i, pairing φ s (B i) ≠ 0 →
      ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div (fun j => pairing φ s (B j)) i z'} ∧
        M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪
          Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) := by
  have hc : ∀ (N : RatModel o Ω') (i : I) (k : K) (z : N.Z), t i ≠ 0 →
      (N.Div (fun k => pairing φ s fun j => v k j / t i ^ e) k z ↔ N.Div (fun k => pairing φ s (v k)) k z) := by
    intro N i k z hi
    simp only [pairing_div]
    exact div_mul_iff (inv_ne_zero ((map_ne_zero φ).2 (pow_ne_zero _ hi)))
  have h1 : ∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z' := fun z' hz' => by
    obtain ⟨i, hi⟩ := ht (f z')
    obtain ⟨k, hk⟩ := hd z'
    exact hf.exists_div_pairing s ((hv _ i hi).symm.trans (hB _ hz')) ((hc M' i k z' hi.1).2 hk)
  refine ⟨h1, fun i hi => ?_⟩
  set R := Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪
    Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) with hR
  have hR1 : ∀ x ∈ M.ringOn W, φ x ∈ R := fun x hx => Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
  have hR2 : ∀ j, pairing φ s (B j) / pairing φ s (B i) ∈ R := fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
  have hfg : R.FG := by
    rw [hR, Algebra.adjoin_union]
    refine Subalgebra.FG.sup ?_ (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    rw [← AlgHom.map_adjoin, Algebra.adjoin_eq]
    exact (fg_ringOn hW hne).map φ
  haveI : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 hfg
  haveI : IsFractionRing R Ω' := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    have hK : Subfield.closure (R : Set Ω') = ⊤ :=
      EE.eq_top_of_pairing_mem hs (hB _ hne.some_mem) hi
        (map_mem_of_ringOn hW hne fun x hx => Subfield.subset_closure (hR1 x hx))
        fun j => Subfield.subset_closure (hR2 j)
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 (hK ▸ Subfield.mem_top x)
    have hle : Subring.closure (R : Set Ω') ≤ R.toSubring := Subring.closure_le.2 le_rfl
    exact ⟨⟨a, hle ha⟩, ⟨b, hle hb⟩, rfl⟩
  have hN : ∀ x ∈ R, ∀ z, x ∈ (ofAffine o Ω' R).O z := fun x hx z => algebraMap_mem_O_ofAffine z (⟨x, hx⟩ : R)
  have hN1 : ∀ x ∈ M.ringOn W, φ x ∈ (ofAffine o Ω' R).ringOn (⊤ : (ofAffine o Ω' R).Z.Opens) :=
    fun x hx => mem_ringOn.2 fun z _ => hN _ (hR1 x hx) z
  obtain ⟨p, hp⟩ : ∃ p, M.IsHom (ofAffine o Ω' R) φ p :=
    exists_isHom_of_local fun z => ⟨⊤, W, trivial, hW, hne, hN1⟩
  have hpW : ∀ z, p z ∈ W := fun z => hp.map_mem_of_ringOn hW hne hN1 trivial
  have hNd : ∀ z, (ofAffine o Ω' R).Div (fun j => pairing φ s (B j)) i z := fun z => ⟨hi, fun j => hN _ (hR2 j) z⟩
  obtain ⟨g, hg⟩ := hu (ofAffine o Ω' R) fun z => by
    obtain ⟨i', hi'⟩ := ht (p z)
    obtain ⟨k, hk⟩ := hp.exists_div_pairing s ((hB _ (hpW z)).symm.trans (hv _ i' hi')) (hNd z)
    exact ⟨(i', k), div_mul_prod_iff.2 ⟨hp.div hi', (hc _ i' k z hi'.1).1 hk⟩⟩
  have hgf : g ≫ f = p := (hf.comp hg).unique hp
  let U : M'.Z.Opens := f ⁻¹ᵁ W ⊓ ⟨_, M'.isOpen_setOf_div (fun j => pairing φ s (B j)) i⟩
  have := isAffineOpen_of_isHom R (U := U) ?_ hg ?_
  · exact ⟨U, this.1, rfl, this.2⟩
  · refine Algebra.adjoin_le ?_
    rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hf.map_mem_O (mem_ringOn.1 hx _ hz.1)
    · exact mem_ringOn.2 fun z hz => hz.2.2 j
  · rintro _ ⟨z, rfl⟩
    have hz : f (g z) ∈ W := by
      have := hpW z
      rwa [← hgf] at this
    obtain ⟨j, hj⟩ := h1 _ hz
    exact ⟨hz, hg.div_of_div hj (hNd z)⟩

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.splitTorus_extension_descends_alt : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  first | exact @GlobalTheory.splitTorus_extension_descends | exact GlobalTheory.splitTorus_extension_descends | (intros; apply GlobalTheory.splitTorus_extension_descends <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.group_structure_descends_along_pullback : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (B : Over (Sp K)) [GrpObj B] (B₀ : Over (Sp k)) (φ : B.left ⟶ B₀.left), IsAbelianScheme B → IsPullback φ B.hom B₀.hom (spMap β) → ∀ (m : B₀ ⊗ B₀ ⟶ B₀) (i : B₀ ⟶ B₀) (e : 𝟙_ (Over (Sp k)) ⟶ B₀) (φ₂ : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left), φ₂ ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ → φ₂ ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ → φ₂ ≫ m.left = (μ[B]).left ≫ φ → φ ≫ i.left = (ι[B]).left ≫ φ → spMap β ≫ e.left = (η[B]).left ≫ φ → ∃ _ : GrpObj B₀, IsAbelianScheme B₀ ∧ IsGrpPullback B B₀ (spMap β) φ := by
  first | exact @GlobalTheory.isAbelianScheme_descends_subfield | exact GlobalTheory.isAbelianScheme_descends_subfield | (intros; apply GlobalTheory.isAbelianScheme_descends_subfield <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt : ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (Sp K)) (X₀ Y₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (spMap σ) → IsPullback ψ Y.hom Y₀.hom (spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (spMap α) → IsPullback ω Y₁.hom Y₀.hom (spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by
  first | exact @GlobalTheory.hom_descends_to_subfield_containing_finset | exact GlobalTheory.hom_descends_to_subfield_containing_finset | (intros; apply GlobalTheory.hom_descends_to_subfield_containing_finset <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by
  first | exact @GlobalTheory.ExtensionRigidity.isMonHom_of_pointed | exact GlobalTheory.ExtensionRigidity.isMonHom_of_pointed | (intros; apply GlobalTheory.ExtensionRigidity.isMonHom_of_pointed <;> assumption)
end
