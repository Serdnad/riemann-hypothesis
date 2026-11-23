module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle280
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle265
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantLemmaDiscreteValuationRingQuotientLen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle267
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

lemma gA_term_le_one (l : ℕ) [Fact l.Prime] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l) (n : ℕ) :
    ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n ≤ 1 := by
  have hx0 : 0 ≤ ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_nonneg _
  have hx1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
  have he : 0 ≤ (1 : ℝ) / (l : ℝ) ^ n := by positivity
  have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
    Real.rpow_le_one hx0 hx1 he
  have h3 : ρ ^ n ≤ 1 := pow_le_one₀ h0 h1
  calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (pow_nonneg h0 n) zero_le_one
    _ = 1 := one_mul 1

theorem gC_teich_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l),
    ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 →
      ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  intro l _ ζ ζ' hζ ρ hρ hρ1
  have hex : ∃ N, IsGauss l ρ N := GlobalTheory.GaussExt.exists_gauss_acris l ρ hρ hρ1
  have hg : IsGauss l ρ (Classical.choose hex) := Classical.choose_spec hex
  have hC : gC l ρ (tc l ζ - tc l ζ') = Classical.choose hex (tc l ζ - tc l ζ') := by
    unfold gC; rw [dite_eq_left hex]
  have hsub : tc l ζ - tc l ζ' =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm ζ - Formalism.Per.tm ζ') := by
    unfold tc; rw [map_sub]
  rw [hC, hsub, hg.2.2.2.2]
  have hl : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  have h0 : 0 ≤ ρ := le_of_lt (lt_of_lt_of_le hl hρ)
  have hc0 : (Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff 0 = ζ - ζ' := by
    have := map_sub (WittVector.constantCoeff (p := l) (R := Formalism.Per.Fl l)) (Formalism.Per.tm ζ) (Formalism.Per.tm ζ')
    simpa [Formalism.Per.tm] using this
  unfold gA
  apply le_antisymm
  · exact ciSup_le (fun n => gA_term_le_one l ρ h0 hρ1.le _ n)
  · have hb : BddAbove (Set.range fun n : ℕ =>
        ‖((((Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
          ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n) :=
      ⟨1, by rintro _ ⟨n, rfl⟩; exact gA_term_le_one l ρ h0 hρ1.le _ n⟩
    refine le_trans ?_ (le_ciSup hb 0)
    simp [hc0, hζ]

end GlobalTheory.PMon.Gauss

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.PotDual

def bundle {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem isDual1_of_eq {k : ℕ} (M U : G →* Matrix (Fin k) (Fin k) LL)
    (hU : ∀ g, U g = ((cycLL PD LL g : LLˣ) : LL) • (M g⁻¹).transpose) :
    IsDual1 PD (matRep M) (matRep U) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (M g).mulVec x ⬝ᵥ ((U g).mulVec y) = ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

end

section

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (Br.loc D.nbr i w hw M) := by
  have hfc : Continuous (D.nbr i w hw).toLL :=
    continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have hι : Continuous fun g : Br.G D.nbr i w hw => ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  exact (hM.comp hι).matrix_map hfc

theorem isDual1_loc (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    IsDual1 ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
      (matRep (Br.loc D.nbr i w hw (rDuO D.nd i r x))) (dotProductBilin _ _) := by
  refine isDual1_of_eq _ _ _ fun g => ?_
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  let f := (D.nbr i w hw).toLL
  have e : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
      ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥(D.nbr i w hw).LL.1 g :
        (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1) :=
    congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
  rw [← e]
  ext a b
  congr 1
  change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
    f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
  rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
  congr 1
  ring

end



theorem stepPotDual : StepPotDual := by
  classical
  intro D hT i r hr Xs w hw n ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hst, h1, hc, hx⟩
  refine ⟨K', h, hN, hF, hS, Sig.image (fun a => a⁻¹), Fr, hFr, ?_, ?_,
    le_trans Finset.card_image_le hc, fun x => ?_⟩
  · intro a ha
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b, hb, hab⟩ := hst a ha'
    refine ⟨b⁻¹, Finset.mem_image.2 ⟨b, hb, rfl⟩, fun g g' hg => ?_⟩
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hab g g' hg]
  · exact Finset.mem_image.2 ⟨1, h1, inv_one⟩
  · have hcont := GlobalTheory.Pass.FamCont.stepCont D i r hr x
    exact (hT (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS
      (bundle _ _ (Br.loc D.nbr i w hw (rTwO D.nd i r x)) (continuous_loc D i w hw _ hcont.1))
      (bundle _ _ (Br.loc D.nbr i w hw (rDuO D.nd i r x)) (continuous_loc D i w hw _ hcont.2))
      Sig (Sig.image (fun a => a⁻¹)) (hx x).1 (hx x).2).2 (dotProductBilin _ _)
      (isDual1_loc D i w hw r x)
      (fun b => by
        rw [Finset.mem_image]
        exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩)

end GlobalTheory.PotDual

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.JumpDual

def matG {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

theorem isDual1_dot {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {k : ℕ} (T U : G →* Matrix (Fin k) (Fin k) LL)
    (hU : ∀ g, U g = ((cycLL PD LL g : LLˣ) : LL) • (T g⁻¹).transpose) :
    IsDual1 PD (matRep T) (matRep U) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (T g).mulVec x ⬝ᵥ ((U g).mulVec y) = ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

theorem loc_cont (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (Br.loc D.nbr i w hw M) := by
  have hfc : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    hM.comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact h1.matrix_map hfc

theorem loc_dual (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw (rDuO D.nd i r x) g =
      ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) •
        (Br.loc D.nbr i w hw (rTwO D.nd i r x) g⁻¹).transpose := by
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  let f := (D.nbr i w hw).toLL
  rw [← GlobalTheory.CycBridge.locChi_epsU D i w hw g]
  ext a b
  congr 1
  change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
    f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
  rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
  congr 1
  ring

theorem jump_dual : ∀ D : D7, DualJumpL D.loc → PotDRL D.loc → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ (x : ↥Xs) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ), IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rDuO D.nd i r x))) τ a ↔ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) τ (-a - 1) := by
  intro D hJ hP i r hr Xs w hw n hF x τ a
  obtain ⟨K', h, hN, hI, hS, Sig, Fr, -, -, -, -, hx⟩ := hF
  have hc := GlobalTheory.T.twisted_dual_families_continuous D i r hr x
  have cT := loc_cont D i w hw _ hc.1
  have cU := loc_cont D i w hw _ hc.2
  have hcr := (GlobalTheory.T.potentiallyCrystalline_module_eq_crystalline_restriction (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hI hS _
    (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))).2.1 (hx x).1
  have hdR := hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h
    (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cT) hcr
  exact hJ (D.nd.l i) (D.nbr i w hw).Kw (D.nbr i w hw).LL
    (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cT) (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cU)
    (dotProductBilin _ _) (isDual1_dot _ _ _ (loc_dual D i w hw r x)) hdR τ a

end GlobalTheory.JumpDual

end
end

section

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem isGauss_gC_of_le (l : ℕ) [Fact l.Prime] (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    IsGauss l ρ (gC l ρ) := by
  have h : ∃ N, IsGauss l ρ N := GlobalTheory.GaussExt.exists_gauss_acris l ρ h0 h1
  have e : gC l ρ = Classical.choose h := by
    funext x
    simp only [gC, dif_pos h]
  rw [e]
  exact Classical.choose_spec h

theorem isGauss_gC_target : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ (gC l ρ) :=
  fun l _ ρ h0 h1 => isGauss_gC_of_le l ρ h0 h1

end GlobalTheory.PMon.Gauss

end
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_class_admissible : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0) →
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) →
    ∀ z : ↥(Z1 (twCoef W S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea W S.Γ.χ₁ ha z)) ↔
        Submodule.Quotient.mk z ∈ S.cls W X) := by
  first | exact @GlobalTheory.admissible_eventually_iff_mem_cls | exact GlobalTheory.admissible_eventually_iff_mem_cls | (intros; apply GlobalTheory.admissible_eventually_iff_mem_cls <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.cutValue_mem_heckeValueIdealOffSupport : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  first | exact @GlobalTheory.Cut.value_mem_ccOff | exact GlobalTheory.Cut.value_mem_ccOff | (intros; apply GlobalTheory.Cut.value_mem_ccOff <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  first | exact @GlobalTheory.Cut.Coc.main | exact GlobalTheory.Cut.Coc.main | (intros; apply GlobalTheory.Cut.Coc.main <;> assumption)
end

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.residualRep_ker_isOpen : ∀ (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by
  first | exact @GlobalTheory.TypeLeaf.redF_ker_isOpen | exact GlobalTheory.TypeLeaf.redF_ker_isOpen | (intros; apply GlobalTheory.TypeLeaf.redF_ker_isOpen <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [Ring A] [Algebra O A] (J : Type) [Fintype J] (d : J → ℕ) (ψ : ∀ j, A →ₐ[O] Matrix (Fin (d j)) (Fin (d j)) O), (∀ j, Function.Surjective (ψ j)) → ∀ (g : ℕ) (Rel : Submodule A (Fin g → A)) (I : Ideal O), (∀ (n : ℕ) (θ : Fin n → Fin g → Fin g → A), (∀ k p, θ k p ∈ Rel) → ∀ m : Fin n →₀ ℕ, AddMonoidAlgebra.coeff (∏ j, Matrix.det (Matrix.of fun (pa qb : Fin g × Fin (d j)) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin n) O) * MvPolynomial.C (ψ j (θ k pa.1 qb.1) pa.2 qb.2))) m ∈ I) → Module.length O (O ⧸ I) ≤ ∑ j, Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ j (θ q))).comp (LinearMap.proj q : (Fin g → KOG O (d j)) →ₗ[O] KOG O (d j)))) := by
  first | exact @GlobalTheory.DetGen.length_quot_le_sum_length | exact GlobalTheory.DetGen.length_quot_le_sum_length | (intros; apply GlobalTheory.DetGen.length_quot_le_sum_length <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.repr_smul_add : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (c : k) (z z' : G → Fin A.m → k) (b g b' g' : ZMod n → Vc k A.m), Repr F A z b g → Repr F A z' b' g' → Repr F A (c • z + z') (c • b + b') (c • g + g') := by
  first | exact @GlobalTheory.TopSteps.Repr.smul_add | exact GlobalTheory.TopSteps.Repr.smul_add | (intros; apply GlobalTheory.TopSteps.Repr.smul_add <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree : ∀ (G : Type) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ), (a * a = a → IsChar χ → ∃ n : ℕ, tr a χ = n) ∧ (IsIrr χ → ∃ d : ℕ, 0 < d ∧ χ 1 = d) ∧ (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  first | exact @GlobalTheory.GLq.trIdem | exact GlobalTheory.GLq.trIdem | (intros; apply GlobalTheory.GLq.trIdem <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime | exact GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime | (intros; apply GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime <;> assumption)
end
