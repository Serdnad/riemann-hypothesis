module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle735
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle718
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle748
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle705
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle750
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle745
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle466
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase

open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix

namespace GlobalTheory.UnifDensTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem aeval_term {κ S : Type} [CommRing S] [Algebra ℝ S] (φ : κ → S) (x : κ) (a s : ℕ) :
    aeval φ ((C ((-1 : ℝ) ^ a) * X x) ^ s) = (algebraMap ℝ S ((-1 : ℝ) ^ a) * φ x) ^ s := by
  rw [map_pow (aeval φ), map_mul (aeval φ), aeval_C, aeval_X]

theorem chernPoly_cast {n a b : ℕ} (hab : a = b) (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    chernPoly (fun u => (G u).submatrix (Fin.cast hab.symm) (Fin.cast hab.symm)) v k = chernPoly G v k := by
  subst hab; rfl

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem chernTop_pointPoly_eq (H : Host E) (Dw : Datum H) {n : ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → Mat Dw.mult ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) :
    chernTop (pointPoly H Dw) G v =
      GlobalTheory.GoodMetric.chernTop (m := fun _ : GlobalTheory.AllWt.Psi H => Dw.p)
        (∏ τ : GlobalTheory.AllWt.Psi H, (MvPolynomial.C ((-1 : ℝ) ^ Dw.p) * MvPolynomial.X (τ, Dw.p)) ^ (Dw.p + Dw.q - Dw.p))
        (fun u τ => (G u τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)
          (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)) v := by
  unfold chernTop
  congr 3
  rw [pointPoly, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [aeval_term, aeval_term]
  erw [chernPoly_cast (GlobalTheory.HodgeGenUnf.mult_psi τ) (fun u => G u τ.1) v Dw.p]
  exact congrArg (fun m => (algebraMap ℝ (MvPolynomial (Fin n × Fin n) ℂ) ((-1 : ℝ) ^ m) *
    chernPoly (fun u => G u τ.1) v m) ^ (Dw.p + Dw.q - m)) (GlobalTheory.HodgeGenUnf.mult_psi τ)

theorem chernTop_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (a : ι → ι') (ha : Function.Bijective a)
    (p s : ℕ) {n : ℕ} (K : ReciprocityTheory.L2DbarEstimates.V n → Mat (fun _ : ι' => p) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p)
                 (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ s) (fun u τ => K u (a τ)) v =
      GlobalTheory.GoodMetric.chernTop (m := fun _ : ι' => p)
        (∏ τ : ι', (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ s) K v := by
  unfold chernTop
  congr 3
  rw [map_prod, map_prod]
  simp only [aeval_term]
  exact Fintype.prod_bijective _ ha _ _ fun τ => rfl

end GlobalTheory.UnifDensTransport

namespace GlobalTheory.UnifDensTransport

theorem letter_bijective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)}
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) :
    Function.Bijective (GlobalTheory.HodgeGenUnf.letter hσ hU k) := by
  obtain ⟨hb, hg, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  refine ⟨fun a b hab => Subtype.ext (hb.1 (congrArg Subtype.val hab)), fun τ' => ?_⟩
  obtain ⟨τ, hτ⟩ := hb.2 τ'.1
  have hm : τ H.rt = H.rt0 := (hg τ).1 (by rw [hτ]; exact ((hU.2.1 k).2 τ'.1).1 τ'.2)
  exact ⟨⟨τ, hm⟩, Subtype.ext hτ⟩

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem chernTop_pointPoly_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : (U.X k).Ψ => Dw.p) (∏ τ : (U.X k).Ψ, (MvPolynomial.C ((-1 : ℝ) ^ Dw.p) * MvPolynomial.X (τ, Dw.p)) ^ (Dw.p + Dw.q - Dw.p)) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  rw [chernTop_pointPoly_eq, ← chernTop_reindex _ (letter_bijective hσ hU k)]
  choose cc hcc g hg hgu hG using GlobalTheory.T.hodge_metric_uniformisation_gram_local_holomorphic E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  exact GlobalTheory.PointChern.chernTop_changeFrame _ _ _ (fun w τ => g τ w) cc v hcc hg hgu
    (fun τ => (GlobalTheory.T.boundedDomainModelMetric_contDiffAt_and_isUnit _ _ _ _ h v hv _).1) (fun τ => (GlobalTheory.T.boundedDomainModelMetric_contDiffAt_and_isUnit _ _ _ _ h v hv _).2) (Filter.eventually_all.2 hG)

end GlobalTheory.UnifDensTransport
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.flagSpaceComponent_refines_lie_frames_graded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] C.Y.Fn), Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  first | exact @GlobalTheory.ShFam.BaseRefine.main | exact GlobalTheory.ShFam.BaseRefine.main | (intros; apply GlobalTheory.ShFam.BaseRefine.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.RatExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Mem.R3.Rw.LiftExt

private theorem comb_gen {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] (Y : HMod E) (X : HMod E')
    (g : Y.H →ₗ[ℂ] X.H) (hinj : Function.Injective Y.e) (v : Y.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g v := by
  have e : v = ∑ k, s k • u k := hinj (by rw [eq_of_heq hv, map_sum]; simp only [map_smul])

  rw [e, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, eq_of_heq (hp k)]

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {V W : HSp a.D} {V' W' : HSp a'.D} {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}

private theorem comb_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W) (h : DSTie M' M) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW)
    {Y : HMod (Bridge.Gf V → c.W)} {Y' : HMod (Bridge.Gf V' → c'.W)} (hY : HEq Y' Y)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X) {g : Y.H →ₗ[ℂ] X.H} {g' : Y'.H →ₗ[ℂ] X'.H} (hg : HEq g' g)
    (hinj : Function.Injective Y.e) (v : Y'.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y'.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X'.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g' v := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (W')) ((by with_unfolding_all exact ((W) :))) (W') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W')) (W') (((W))) (((hW)))).symm : _))
  clear (hW)
  subst e))
  obtain ⟨H', s', l', ε', f', _, _, _, _⟩ := M'
  rename_i n' i' _ _ _ _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((M.H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((M.H))) (((h1)))).symm : _))
  clear (h1)
  subst e))
  ( (
  have e : @Eq (type_of% (n')) ((by with_unfolding_all exact ((M.nacg) :))) (n') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (n')) (n') (((M.nacg))) (((h2)))).symm : _))
  clear (h2)
  subst e))
  ( (
  have e : @Eq (type_of% (i')) ((by with_unfolding_all exact ((M.ips) :))) (i') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (i')) (i') (((M.ips))) (((h3)))).symm : _))
  clear (h3)
  subst e))
  ( (
  have e : @Eq (type_of% (s')) ((by with_unfolding_all exact ((M.σ) :))) (s') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (s')) (s') (((M.σ))) (((h4)))).symm : _))
  clear (h4)
  subst e))
  ( (
  have e : @Eq (type_of% (l')) ((by with_unfolding_all exact ((M.lam) :))) (l') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (l')) (l') (((M.lam))) (((h5)))).symm : _))
  clear (h5)
  subst e))
  ( (
  have e : @Eq (type_of% (ε')) ((by with_unfolding_all exact ((M.ε) :))) (ε') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ε')) (ε') (((M.ε))) (((h6)))).symm : _))
  clear (h6)
  subst e))
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((M.fr) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((M.fr))) (((h7)))).symm : _))
  clear (h7)
  subst e))
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ( (
  have e : @Eq (type_of% (W₁)) ((by with_unfolding_all exact ((c.W) :))) (W₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W₁)) (W₁) (((c.W))) (((c1)))).symm : _))
  clear (c1)
  subst e))
  ( (
  have e : @Eq (type_of% (nW')) ((by with_unfolding_all exact ((c.nW) :))) (nW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nW')) (nW') (((c.nW))) (((c3)))).symm : _))
  clear (c3)
  subst e))
  ( (
  have e : @Eq (type_of% (iW')) ((by with_unfolding_all exact ((c.iW) :))) (iW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (iW')) (iW') (((c.iW))) (((c4)))).symm : _))
  clear (c4)
  subst e))
  ( (
  have e : @Eq (type_of% (ρ₁)) ((by with_unfolding_all exact ((c.ρ) :))) (ρ₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ρ₁)) (ρ₁) (((c.ρ))) (((c2)))).symm : _))
  clear (c2)
  subst e))
  ( (
  have e : @Eq (type_of% (Y')) ((by with_unfolding_all exact ((Y) :))) (Y') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Y')) (Y') (((Y))) (((hY)))).symm : _))
  clear (hY)
  subst e))
  ( (
  have e : @Eq (type_of% (X')) ((by with_unfolding_all exact ((X) :))) (X') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (X')) (X') (((X))) (((hX)))).symm : _))
  clear (hX)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  exact (by with_unfolding_all exact ((comb_gen Y X g hinj ((v)) s u ((hv)) ((p)) ((hp))) : _))

end Comparison₂

private theorem apply_eq {m m' : ℕ} (hm : m' = m) {F : Fin m → ℕ} {F' : Fin m' → ℕ} (hF : HEq F' F) {i : Fin m} {i' : Fin m'}
    (h : (i : ℕ) = i') : F i = F' i' := by
  subst hm
  obtain rfl := eq_of_heq hF
  obtain rfl : i = i' := Fin.ext h
  rfl

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}



private theorem rat_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW)
    (hM : DSTie (R'.MW i' a'.D.what₂.embLL) (R.MW i a.D.what₂.embLL)) (hHW : HEq (R'.HW i' a'.D.what₂.embLL) (R.HW i a.D.what₂.embLL))
    (hHV : HEq (R'.HV i' t') (R.HV i t)) (hg : HEq (R'.thG i' t') (R.thG i t)) (hn : HEq R'.nW R.nW)
    (ι : a.D.what₂.LL →+* a'.D.what₂.LL) (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x)
    (hj : ∀ (σ' : a'.D.what₂.LL →+* ℂ) x x', CrdOver ι x x' → HEq ((R'.FW i').j σ' x') ((R.FW i).j (σ'.comp ι) x))
    (hinj : Function.Injective (R.HV i t).e) (hjV : ∀ x, (R.HV i t).e (R.jV i t x) = R.B.jL i t x) (hr : RatAt R t)
    (x' : A'.fam.amb.FL i' t') {n : ℕ} (b : Fin n → a'.D.what₂.LL) (x : Fin n → A.fam.amb.FL i t)
    (hx : HEq (R'.B.jL i' t' x') (∑ k, a'.D.what₂.embLL (b k) • R.B.jL i t (x k)))
    (v : (R'.HV i' t').H) (hv : (R'.HV i' t').e v = R'.B.jL i' t' x') :
    ∃ y, (R'.FW i').j (sg0 a'.D A') y = R'.thG i' t' v := by
  have s : a.D.what₂.embLL = sg0 a.D A := (sgAt_mk _ R.hv0).symm
  have s' : a'.D.what₂.embLL = sg0 a'.D A' := (sgAt_mk _ R'.hv0).symm
  have hM0 : DSTie (R'.MW i' (sg0 a'.D A')) (R.MW i (sg0 a.D A)) := s ▸ s' ▸ hM
  have hHW0 : HEq (R'.HW i' (sg0 a'.D A')) (R.HW i (sg0 a.D A)) := s ▸ s' ▸ hHW
  have hc : (sg0 a'.D A').comp ι = sg0 a.D A := by
    rw [← s, ← s']; exact RingHom.ext hι
  have hmv : ∀ (σ₁ σ₂ : a.D.what₂.LL →+* ℂ), σ₁ = σ₂ → ∀ y, HEq ((R.FW i).j σ₁ y) ((R.FW i).j σ₂ y) := by
    intro σ₁ σ₂ e y; subst e; exact HEq.rfl
  have hn0 : R.nW i = R'.nW i' := apply_eq (LiftExt.m_eq hP) hn h
  choose y hy using fun k => hr i (x k) (R.jV i t (x k)) (hjV (x k))
  refine ⟨∑ k, b k • GeoFW.crdMap ι hn0 (y k), ?_⟩
  refine ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => LinearMap.map_smulₛₗ _ _ _)).trans ?_
  refine comb_of hP (vc_heq hP h) (wc_heq hP h) hM0 c1 c2 c3 c4 hHV hHW0 hg hinj v (fun k => sg0 a'.D A' (b k))
    (fun k => R.jV i t (x k)) ?_ (fun k => (R'.FW i').j (sg0 a'.D A') (GeoFW.crdMap ι hn0 (y k))) fun k => ?_
  · refine (heq_of_eq hv).trans (hx.trans (heq_of_eq ?_))
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (by with_unfolding_all exact ((congrArg₂ (fun (c : ℂ) (q : Bridge.Gf (Vc a.D i) → (R.cV i).W) => c • q) (DFunLike.congr_fun s' (b k)) (hjV (x k)).symm) :))
  · exact ((hj _ _ _ (GeoFW.crdOver_crdMap ι hn0 (y k))).trans (hmv _ _ hc _)).trans (heq_of_eq (hy k))

end Fields

end GlobalTheory.Mem.R3.Rw.RatExt


theorem _root_.GlobalTheory.T.referenceTuple_rationalForm_lifts_algebraic_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSide z Wt' R' → JSpan z Wt' R' → RatAt z.R.toRealDat (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) → RatAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hS hJ hr i' x' v hv
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  obtain ⟨⟨-, -, -, -, -, hn, -, -, -, -, -, -, h1, -⟩, h2⟩ := hS
  obtain ⟨c1, c2, c3, c4, -, -, -, m1, m2, m3, m4, m5, m6, m7, -, hHW, -, -, hWι⟩ := h1 i i' h
  obtain ⟨-, -, hHV, -, hg, -, -⟩ := h2 i i' h
  obtain ⟨n, b, x, hx⟩ := hJ i i' h x'
  have hb := z.pins.char.base.models
  exact RatExt.rat_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h c1 c2 c3 c4
    ⟨m1, m2, m3, m4, m5, m6, m7⟩ hHW hHV hg hn ι hι (fun σ' => ((hWι ι hι).1 σ').2.2.2) (hb.HV i _).1 (hb.jV i _) hr x' b x hx v hv
end
