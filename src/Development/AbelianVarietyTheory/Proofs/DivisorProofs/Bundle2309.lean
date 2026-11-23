module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle023
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J), (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧ (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧ filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧ ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n)) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (I : Ideal R) (κ : DividedPowers I), IsDPMorphism κ δ (algebraMap R B) → J ≤ I.map (algebraMap R B) → rel R δ = ⊥ := by
  first | exact @GlobalTheory.PDForm.rel_two_sided_and_bot | exact GlobalTheory.PDForm.rel_two_sided_and_bot | (intros; apply GlobalTheory.PDForm.rel_two_sided_and_bot <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS.LinTan

open GlobalTheory.FlagMod

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem le_preimage_top {T Z : Scheme.{0}} (z : T ⟶ Z) : ⊤ ≤ z ⁻¹ᵁ ⊤ := le_rfl

theorem eq_of_ev {Y : Scheme.{0}} {S : Type} [CommRing S] {U : Y.Opens} (hU : IsAffineOpen U) {z z' : Sp S ⟶ Y}
    (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ z' ⁻¹ᵁ U) (e : ∀ f, ev z U h f = ev z' U h' f) : z = z' := by
  rw [← spMap_ev z hU h, ← spMap_ev z' hU h', RingHom.ext e]

theorem le_preimage_of_fst {Y : Scheme.{0}} {B : Type} [CommRing B] {n : ℕ} {x : Sp B ⟶ Y}
    {w : Sp (TrivSqZeroExt B (Fin n → B)) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) :
    ⊤ ≤ w ⁻¹ᵁ O := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (TrivSqZeroExt B (Fin n → B))) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← hw] at this
  exact this

theorem exists_glue {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A →+* B) (d : Fin n → (A →+* DualNumber B))
    (hd : ∀ a f, (d a f).fst = e f) : ∃ q : A →+* TrivSqZeroExt B (Fin n → B),
      ∀ f, (q f).fst = e f ∧ ∀ a, (q f).snd a = (d a f).snd := by
  refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr fun a => (d a f).snd,
            map_one' := ?_, map_mul' := fun f g => ?_,
            map_zero' := ?_, map_add' := fun f g => ?_ }, fun f => ⟨add_zero (e f), fun a => zero_add (d a f).snd⟩⟩
  · ext <;> simp
  · ext
    · simp
    · simp [hd, mul_comm]
  · ext <;> simp
  · ext <;> simp

theorem exists_linComb {K B : Type} [CommRing K] [CommRing B] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (Y₀ : Y.affineOpens)
    (φ : K →+* B) (x : Sp B ⟶ Y) (hx : x ≫ p = spMap φ) (hxY : ⊤ ≤ x ⁻¹ᵁ Y₀.1) {n : ℕ}
    (w : Fin n → (Sp (DualNumber B) ⟶ Y)) (hwp : ∀ a, w a ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ))
    (hwx : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w a = x) (c : Fin n → B) :
    ∃ S : Sp (DualNumber B) ⟶ Y, S ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ) ∧
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x ∧
      ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O), (valR S O f).snd = ∑ a, c a * (valR (w a) O f).snd := by
  have hwY : ∀ a, ⊤ ≤ w a ⁻¹ᵁ Y₀.1 := fun a => le_preimage_of_red (hwx a) hxY
  obtain ⟨q, hq⟩ := exists_glue (ev x Y₀.1 hxY) (fun a => ev (w a) Y₀.1 (hwY a)) (fun a f => by
    have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (w a) Y₀.1 (hwY a) (le_preimage_comp _ (hwY a))
    rw [ev_congr (hwx a) _ _ hxY] at this
    rw [this]; rfl)
  let T : Sp (TrivSqZeroExt B (Fin n → B)) ⟶ Y := spMap q ≫ tau Y₀.2
  have hT : ∀ {S : Type} [CommRing S] (σ : TrivSqZeroExt B (Fin n → B) →+* S) (z : Sp S ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ Y₀.1),
      (∀ f, σ (q f) = ev z Y₀.1 hz f) → spMap σ ≫ T = z := fun σ z hz e => by
    rw [← spMap_ev z Y₀.2 hz, ← RingHom.ext (f := σ.comp q) e, ← spMap_comp_spMap, Category.assoc]
    rfl
  let σ : ((Fin n → B) →ₗ[B] B) → (TrivSqZeroExt B (Fin n → B) →+* DualNumber B) := fun l =>
    (TrivSqZeroExt.map l).toRingHom
  have hσ1 : ∀ l r, (σ l r).fst = r.fst := fun l r => TrivSqZeroExt.fst_map l r
  have hσ2 : ∀ l r, (σ l r).snd = l r.snd := fun l r => TrivSqZeroExt.snd_map l r
  have hTx : spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom ≫ T = x := hT _ x hxY fun f => (hq f).1
  have hTw : ∀ a, spMap (σ (LinearMap.proj a)) ≫ T = w a := fun a => hT _ _ (hwY a) fun f => by
    ext
    · rw [hσ1, (hq f).1]
      have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (w a) Y₀.1 (hwY a) (le_preimage_comp _ (hwY a))
      rw [ev_congr (hwx a) _ _ hxY] at this
      rw [this]; rfl
    · rw [hσ2]; exact (hq f).2 a
  let l : (Fin n → B) →ₗ[B] B := Fintype.linearCombination B c
  have hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (spMap (σ l) ≫ T) = x := by
    rw [← Category.assoc, spMap_comp_spMap, ← hTx]
    congr 2
    exact RingHom.ext fun r => hσ1 l r
  have hS : ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O),
      (valR (spMap (σ l) ≫ T) O f).snd = ∑ a, c a * (valR (w a) O f).snd := fun O hO f => by
    have hTO : ⊤ ≤ T ⁻¹ᵁ O := le_preimage_of_fst hTx hO
    have key : ∀ l', valR (spMap (σ l') ≫ T) O f = σ l' (ev T O hTO f) := fun l' => by
      rw [valR_eq_ev _ _ (le_preimage_comp _ hTO), ev_spMap _ _ _ hTO]; rfl
    rw [key, hσ2, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hTw a, key, hσ2, smul_eq_mul, mul_comm]; rfl
  refine ⟨spMap (σ l) ≫ T, ?_, hSx, hS⟩
  have hv : ∀ {S : Type} [CommRing S] (ψ : K →+* S) (f : Γ(Sp K, ⊤)),
      valR (spMap ψ) ⊤ f = ψ (ev (𝟙 (Sp K)) ⊤ (le_preimage_top _) f) := fun ψ f => by
    rw [← Category.comp_id (spMap ψ), valR_eq_ev _ _ (le_preimage_top _), ev_spMap _ _ _ (le_preimage_top _)]; rfl
  refine eq_of_ev (isAffineOpen_top (Sp K)) (le_preimage_top _) (le_preimage_top _) fun f => ?_
  rw [← valR_eq_ev, ← valR_eq_ev, hv]
  ext
  · have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom ((spMap (σ l) ≫ T) ≫ p) ⊤ (le_preimage_top _) (le_preimage_top _)
    rw [ev_congr (z' := spMap φ) (by rw [← Category.assoc, hSx, hx]) _ _ (le_preimage_top _)] at this
    have h2 := RingHom.congr_fun this f
    rw [← valR_eq_ev, hv] at h2
    rw [valR_eq_ev _ _ (le_preimage_top _)]
    exact h2.symm
  · rw [valR_comp_app, hS (p ⁻¹ᵁ ⊤) (le_preimage_top (x ≫ p))]
    simp only [← valR_comp_app, hwp, hv]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.CechKS.LinTan
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.QuadSum

variable {K : Type} [Field K]

theorem hom_finset_sum {B A : AbVar K} {J : Type} (s : Finset J) (g : J → (B ⟶ A)) :
    Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i ∈ s, g i) = ∏ i ∈ s, (g i).hom := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, add_hom, ih]

theorem lam_symm {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  unfold AbVar.lam
  rw [mul_comm x y]
  abel

theorem lam_prod_right {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x : Y ⟶ A.X) {J : Type}
    (s : Finset J) (y : J → (Y ⟶ A.X)) :
    AbVar.lam c x (∏ j ∈ s, y j) = ∑ j ∈ s, AbVar.lam c x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x 1 1 0).2.2.1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x (y a) _ 0).1, ih]

theorem lam_prod_left {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} {J : Type}
    (s : Finset J) (x : J → (Y ⟶ A.X)) (y : Y ⟶ A.X) :
    AbVar.lam c (∏ i ∈ s, x i) y = ∑ i ∈ s, AbVar.lam c (x i) y := by
  rw [lam_symm, lam_prod_right]
  exact Finset.sum_congr rfl (fun i _ => lam_symm c y (x i))

theorem lam_zpow_zpow {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) (m n : ℤ) :
    AbVar.lam c (x ^ m) (y ^ n) = (m * n) • AbVar.lam c x y := by
  rw [(GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y (x ^ m) y y n).2.2.2.2, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x y y m).2.2.2.1, smul_smul,
    mul_comm n m]

end GlobalTheory.AV.QuadSum

theorem GlobalTheory.AV.QuadSum.pull_sum_smul : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  intro K _ B A c hc n f m
  rw [← (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K B A c hc (∑ i, m i • f i) 1).1, QuadSum.hom_finset_sum, QuadSum.lam_prod_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [QuadSum.lam_prod_right]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [zsmul_hom, zsmul_hom, QuadSum.lam_zpow_zpow]
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

theorem formallyEtale_eval₂Hom_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {r : ℕ}
    {τ : Fin r → F} (hτ : TrBasis c τ) : (MvPolynomial.eval₂Hom c τ).FormallyEtale := by
  letI := c.toAlgebra
  have hτ' : IsTranscendenceBasis ℂ τ := hτ
  have hv := hτ'.1
  let P := MvPolynomial (Fin r) ℂ
  let A := Algebra.adjoin ℂ (Set.range τ)
  let Lf := IntermediateField.adjoin ℂ (Set.range τ)
  haveI := hτ'.isAlgebraic_field
  haveI : Algebra.IsSeparable Lf F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let f1 : P →+* A := hv.aevalEquiv.toAlgHom.toRingHom
  have h1 : f1.FormallyEtale := by
    letI : Algebra P A := f1.toAlgebra
    show Algebra.FormallyEtale P A
    exact .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have h2 : (algebraMap A Lf).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (.of_isLocalization (nonZeroDivisors A))
  have h3 : (algebraMap Lf F).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isSeparable Lf F)
  have hc := RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp h1 h2) h3
  convert hc using 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change c a = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.C a)))
    have hAF : ∀ y : A, algebraMap Lf F (algebraMap A Lf y) = algebraMap A F y := fun y => rfl
    rw [hAF, hv.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  · intro i
    simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    change τ i = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.X i)))
    have := hv.algebraMap_aevalEquiv (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X] at this
    rw [← this]
    rfl

theorem exists_basis_omega_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {n : ℕ}
    {x : Fin n → F} (hx : TrBasis c x) :
    ∃ b : Module.Basis (Fin n) F (Omega c), ∀ i, b i = dFun c (x i) := by
  letI := c.toAlgebra
  have hx' : IsTranscendenceBasis ℂ x := hx
  haveI := hx'.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range x)) F :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact exists_basis_kaehler_of_algebraicIndependent hx'.1

end GlobalTheory.DiagLoc

namespace GlobalTheory.DiagLoc

theorem isFreeGen_dForm_graph : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n k' x τ' hc _ _ hx hτ
  let β := (algebraMap ℂ L).codRestrict (loc L σ) hc
  let ρ : K →+* loc L σ := (toLoc L σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hρ : ρ.comp (algebraMap ℂ K) = β := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨b, hb⟩ := exists_basis_omega_of_trBasis (algebraMap ℂ K) hx
  have hg := formallyEtale_mvPolynomial_eval₂_tensor (R := K) τ'
    (formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)
  have hl : (toLoc L σ).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization (ker σ).primeCompl)
  have hφ : (MvPolynomial.eval₂Hom ρ (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i))).FormallyEtale := by
    convert RingHom.FormallyEtale.comp hg hl using 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ]
    · intro i
      simp
  exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial (algebraMap ℂ K) β ρ hρ x b hb
    (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) hφ

end GlobalTheory.DiagLoc
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)), evO G ((G.left.presheaf.germ O (origin G) hO).hom (dd O f)) = tanDer G v ((G.left.presheaf.germ O (origin G) hO).hom f) := by
  first | exact @GlobalTheory.CoordsOrigin.evO_germ_of_isInv | exact GlobalTheory.CoordsOrigin.evO_germ_of_isInv | (intros; apply GlobalTheory.CoordsOrigin.evO_germ_of_isInv <;> assumption)
end

section

set_option autoImplicit false

namespace GlobalTheory.HSShort

theorem bertiniNF_of_bertini (h : Bertini) : BertiniNF := by
  intro F _ _ T hg hb δ f hf
  obtain ⟨hδ, Q, hQ, hs⟩ := h F T hg hb δ f hf
  exact ⟨hδ, Q, hQ, fun E _ _ _ s hsQ => hs E s hsQ⟩

theorem bertiniNumberField_of_hilbertSamuel : GlobalTheory.HSCore.Quoted → BertiniNF :=
  fun hq => bertiniNF_of_bertini (GlobalTheory.T.bertini_simple_zeros_generic_sections hq)

end GlobalTheory.HSShort
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.smooth_coordinateStratum_etaleChart : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ J : Finset (Fin n), ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  first | exact @GlobalTheory.PairStep.smooth_coordStratum | exact GlobalTheory.PairStep.smooth_coordStratum | (intros; apply GlobalTheory.PairStep.smooth_coordStratum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FockCompare GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

theorem vacuum_real_form : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) ∧ θ ≠ 0 ∧ ∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → f w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * θ (δ • (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) := by
  intro D T L sc G W U N δ hC hδ t j hj f hf
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hf.2.inf
  have hU : ∀ X τ, IsUnit (N.frC X τ).det := fun X τ => by
    show IsUnit ((tauE D τ).mapMatrix (N.fr X).1).det
    rw [← RingHom.map_det]
    exact (Matrix.isUnits_det_units (N.fr X)).map _
  have hs : ∀ Z : D.what₂.Tau → Fin (G.pT (.top t j)).rank → Fin (G.pS (.top t j)).rank → ℂ, δ⁻¹ • δ • Z = Z :=
    fun Z => inv_smul_smul₀ hδ Z
  refine ⟨thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (GlobalTheory.T.differentiable_fockVacuum_gaussian_definitePair W N σ hσ t j hj f hf).comp (differentiable_id.const_smul δ⁻¹)
  · exact GlobalTheory.T.vacuum_realRestriction_satisfies_standardThetaLaw W N σ δ hσ hC hδ t j hj f hf
  · obtain ⟨z, hz⟩ := GlobalTheory.T.definite_pair_unit_vacuum_real_point_ne_zero W N σ hσ t j hj f hf
    intro h0
    apply hz
    have e : thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ
        (δ • fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ : Matrix _ _ ℂ)) = 0 :=
      congrFun h0 _
    unfold thY gZ at e
    erw [hs] at e
    rw [mul_eq_zero] at e
    rcases e with e | e
    · convert e using 3
      funext τ
      simp only [frPt, Matrix.of_apply]
      rw [show Matrix.of ((N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ) =
        (N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ from rfl,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    · exact absurd e (Complex.exp_ne_zero _)
  · intro w hw
    unfold thY gZ
    erw [hs]
    have e1 : frPt (N.frC (.top j)) (N.frC (.top (j + 1)))
        (fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ : Matrix _ _ ℂ)) =
        piW W.θ (G.pT (.top t j)) (G.pS (.top t j)) w := by
      funext τ
      simp only [frPt]
      rw [show Matrix.of ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) =
        (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ from rfl,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b,
        ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * Formalism.L2.Pj.xiR D * sqSum (fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ : Matrix _ _ ℂ)) : ℝ) : ℂ) = 0 := by
      simp only [sqSum]
      push_cast
      ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.VacRealForm
end

section

set_option autoImplicit false

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem om_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (Om Z)).FG := by
  intro E _ _ _ H Dw l Xo c r U _ Z
  exact fnFG_of Xo c (kapFG_pf Xo c) Z

end GlobalTheory.DegVal
end
