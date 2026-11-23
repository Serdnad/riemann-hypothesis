module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.PhragmenLindelof
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

theorem basis_fixed_bc {L k : Type} [CommRing L] [CommRing k] (ψ : L →+* k) {n m : ℕ}
    (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)) (hP : ∀ c, P (P c) = P c)
    (h : ∀ c, P' (ψ ∘ c) = ψ ∘ P c) (e : Fin m → Fin n → L) (he : ∀ i, P (e i) = e i)
    (hb : ∀ c, P c = c → ∃! a : Fin m → L, c = ∑ i, a i • e i) (c' : Fin n → k) (hc : P' c' = c') :
    ∃! a : Fin m → k, c' = ∑ i, a i • (ψ ∘ e i) := by
  classical
  choose M hM using fun j : Fin n => (hb _ (hP (Pi.single j 1))).exists
  have hs : ∀ {R : Type} [CommRing R] (a : Fin n → R), ∑ j, a j • (Pi.single j 1 : Fin n → R) = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hinv : ∀ i, (fun i' => ∑ j, e i j * M j i') = Pi.single i 1 := fun i => by
    refine (hb _ (he i)).unique ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← he i, ← hs (e i), map_sum]
      simp only [map_smul, hM, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    · simp [Pi.single_apply]
  have h1 : ∀ j, P' (Pi.single j 1) = ∑ i, ψ (M j i) • (ψ ∘ e i) := fun j => by
    rw [show (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 from funext fun j' => by
      by_cases hj : j' = j <;> simp [hj, Pi.single_apply], h, hM]
    funext r
    simp [Finset.sum_apply]
  refine ⟨fun i => ∑ j, c' j * ψ (M j i), ?_, fun a ha => ?_⟩
  · show c' = _

    conv_lhs => rw [← hc, ← hs c', map_sum]
    simp only [map_smul, h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  · funext i
    have h2 : ∀ i', ∑ j, ψ (e i' j) * ψ (M j i) = if i = i' then 1 else 0 := fun i' => by
      have := congrArg ψ (congrFun (hinv i') i)
      simpa [Pi.single_apply, apply_ite ψ] using this
    have h3 : ∀ j, c' j = ∑ i', a i' * ψ (e i' j) := fun j => by
      have := congrFun ha j
      simpa [Finset.sum_apply] using this
    show a i = ∑ j, c' j * ψ (M j i)
    simp only [h3, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, h2]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {l : Level H} (c : Coeff l)

theorem exists_proj_bc {L : Type} [CommRing L] [IsLocalRing L] (φ : c.F →+* L) {x : Sp L ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G} (hx : IsUnivChart _ n xc)
    {k : Type} [CommRing k] (ψ : L →+* k) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback (spMap ψ ≫ x)).obj t.G)
      (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, vec t (spMap ψ ≫ x) xc' (ψ ∘ cc) =
        spMap (Formalism.L2.Pj.dualMap ψ) ≫ vec t x xc cc) ∧
      ∀ τ, ∃ (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)), (∀ cc, P (P cc) = P cc) ∧
        (∀ cc, P' (ψ ∘ cc) = ψ ∘ P cc) ∧ (∀ cc, P cc = cc ↔ cc ∈ eig c φ hx τ) ∧
        ∀ cc, P' cc = cc ↔ cc ∈ eig c (ψ.comp φ) hx' τ := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ (τ : E →+* ℂ) {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ X}
      {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G}
      (hx : IsUnivChart _ n xc), (∀ m, proj (rho hx) (embK c) α τ (proj (rho hx) (embK c) α τ m) =
          proj (rho hx) (embK c) α τ m) ∧
        ∀ m, proj (rho hx) (embK c) α τ m = m ↔ m ∈ eig c (algebraMap c.F R) hx τ :=
    fun τ {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) (proj (rho hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) m → proj (rho hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rho hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨fun m => e₂ _ (e₁ m), fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun h => h ▸ e₁ m, fun h => e₂ m h⟩
  letI : Algebra c.F L := φ.toAlgebra
  letI : Algebra L k := ψ.toAlgebra
  letI : Algebra c.F k := (ψ.comp φ).toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (algebraMap L k ∘ cc) = algebraMap L k ∘ rho hx a cc :=
    fun a cc => vec_inj hx' (by
      show vec t _ xc' (tmap hx' _ _) = vec t _ xc' (_ ∘ tmap hx _ _)
      rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
  have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rho hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  exact ⟨xc', hx', hv, fun τ => ⟨_, _, (key τ hx).1, pr _, (key τ hx).2, (key τ hx').2⟩⟩

end GlobalTheory.ShFam.EigStable


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in
theorem GlobalTheory.ShFam.EigStable.stable_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x), IsLocalRing R → GlobalTheory.ShFam.EigFrame.Stable f := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f _ R' _ _ ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  obtain ⟨xc', hx', hv, hP⟩ := GlobalTheory.ShFam.EigStable.exists_proj_bc c φ hx ψ
  choose e he using fun τ i => vec_exists hx (f.v τ i) (f.tan τ i)
  choose P P' hPP hc hP hP' using hP
  have heig : ∀ τ i, P τ (e τ i) = e τ i := fun τ i =>
    (hP τ _).2 ((vec_eig_iff hx _ _).1 (by rw [← he]; exact f.eig τ i))
  have hfv : ∀ τ, f.v τ = fun i => vec Z.t x xc (e τ i) := fun τ => funext (he τ)
  refine ⟨⟨fun τ i => vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ e τ i), fun τ i => vec_tan hx' _,
    fun τ i => (vec_eig_iff hx' _ _).2 ((hP' τ _).1 (by rw [hc, heig])), fun τ w hw hw' => ?_⟩,
    fun τ i => by rw [he]; exact hv _⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  simp only [comb_iff hx']
  refine GlobalTheory.ShFam.EigStable.basis_fixed_bc ψ (P τ) (P' τ) (hPP τ) (hc τ) (e τ) (heig τ) (fun c₀ h₀ => ?_) cc
    ((hP' τ _).2 ((vec_eig_iff hx' _ _).1 hw'))
  have := f.basis τ _ (vec_tan hx c₀) ((vec_eig_iff hx _ _).2 ((hP τ _).1 h₀))
  rw [hfv] at this
  simpa only [comb_iff hx] using this
end
end

section

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom

namespace GlobalTheory.CuspStep

theorem half_plane_bound {g : ℂ → ℂ} {M C : ℝ} (hd : DifferentiableOn ℂ g {z | 0 ≤ z.re})
    (hM : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ M) (hC : ∀ y : ℝ, ‖g (y * I)‖ ≤ C) : ‖g 1‖ ≤ C := by
  refine PhragmenLindelof.right_half_plane_of_bounded_on_real (f := g) ?_ ⟨0, by norm_num, 0, ?_⟩ ?_ hC (by simp)
  · refine DifferentiableOn.diffContOnCl ?_
    rw [Complex.closure_setOf_lt_re]
    exact hd
  · refine Asymptotics.IsBigO.of_bound M ?_
    refine Filter.Eventually.filter_mono inf_le_right ?_
    rw [Filter.eventually_principal]
    intro z hz
    simpa using hM z (le_of_lt hz)
  · refine ⟨M, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
    exact hM y (by simpa using hy)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem differentiable_flow (ξ : Fin r → E) (a : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    Differentiable ℂ (fun z : ℂ => X.flow ξ (fun τ => z * a τ) x) := by
  refine differentiable_pi.mpr fun τ => differentiable_pi.mpr fun i => differentiable_pi.mpr fun j => ?_
  simp only [Data.flow, Data.flowMat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem nfac_flow_real (la : Wt X.Ψ r) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℂ) (hs : ∀ τ, (s τ).im = 0) : X.nfac la (X.flow ξ s x) = X.nfac la x := by
  have hd : X.flow ξ s x ∈ X.dom :=
    FjCauchy.flow_mem_dom X hξ hx s fun τ => by rw [hs, add_zero]; exact FjCauchy.tt_pos X hξ hx τ
  have h := m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx s hd
  simp only [hs, zero_div, add_zero, inv_one, min_self, max_self, Real.one_rpow, Finset.prod_const_one] at h
  have h1 : X.nfac la x / X.nfac la (X.flow ξ s x) = 1 := le_antisymm h.2 h.1
  have hn := FlowCoefficientBounds.nfac_pos X hd la
  rw [div_eq_one_iff_eq hn.ne'] at h1
  exact h1.symm

theorem norm_flow_le {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hF : FreqNonneg X la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    ‖P (X.flow ξ s x)‖ ≤ ∑' ν : X.Ψ → ℝ, ‖X.fj la ξ ν P x‖ := by
  have hd : X.flow ξ s x ∈ X.dom :=
    FjCauchy.flow_mem_dom X hξ hx s fun τ => add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx τ) (hs τ)
  have h0 := m3bExp_holds r X la P hP ξ hξ x hx 0 (by rw [EmbeddingHermitianPairs.flow_zero]; exact hx)
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0
  have hsum : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖ := summable_norm_iff.mpr h0.summable
  have h1 := m3bExp_holds r X la P hP ξ hξ x hx s hd
  refine h1.norm_le_of_bounded hsum.hasSum fun ν => ?_
  by_cases hz : X.fj la ξ ν P x = 0
  · simp [hz]
  · have hν := hF ξ hξ ν x hx hz
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hsn : 0 ≤ ∑ τ, ν τ * (s τ).im := Finset.sum_nonneg fun τ _ => mul_nonneg (hν τ) (hs τ)
    have : (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ).re = -(4 * Real.pi * ∑ τ, ν τ * (s τ).im) := by
      simp [Complex.mul_re, Complex.mul_im, Complex.im_sum]
    rw [this]
    have := Real.pi_pos
    have : 0 ≤ 4 * Real.pi * ∑ τ, ν τ * (s τ).im := by positivity
    linarith

theorem stepBound (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (w : ℝ) (hP : X.IsSec la P) (hF : FreqNonneg X la P)
    (hw : ∀ τ, X.spread la τ / 2 ≤ w) : StepBound X w (X.pnorm la P) := by
  intro ξ hξ x hx q hq B hB
  have ht := FjCauchy.tt_pos X hξ hx
  set b : X.Ψ → ℂ := fun τ => I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ) with hb
  have hbim : ∀ τ, (b τ).im = (q τ - 1) * X.tt ξ x τ := fun τ => by
    simp only [hb, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hbre : ∀ τ, (b τ).re = 0 := fun τ => by
    simp only [hb, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hbn : ∀ τ, (b τ).im ≤ 0 := fun τ => by
    rw [hbim]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(hq τ).2]) (ht τ).le
  have hx' : X.flow ξ b x ∈ X.dom := FjCauchy.flow_mem_dom X hξ hx b fun τ => by
    rw [hbim]; nlinarith [mul_pos (hq τ).1 (ht τ)]
  set x' := X.flow ξ b x with hx'def
  have hn' := FlowCoefficientBounds.nfac_pos X hx' la
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  have him : ∀ z : ℂ, 0 ≤ z.re → ∀ τ, 0 ≤ (z * -b τ).im := fun z hz τ => by
    simp only [Complex.mul_im, Complex.neg_im, Complex.neg_re, hbre, neg_zero, mul_zero, add_zero]
    exact mul_nonneg hz (by linarith [hbn τ])
  have hreal : ∀ y : ℝ, ‖P (X.flow ξ (fun τ => (y * I) * -b τ) x')‖ ≤ B / X.nfac la x' := fun y => by
    have hs : ∀ τ, ((y * I : ℂ) * -b τ).im = 0 := fun τ => by simp [hbre]
    rw [le_div_iff₀ hn', ← nfac_flow_real X la hξ hx' _ hs]
    have h := hB fun τ => ((y * I : ℂ) * -b τ).re
    have he : X.flow ξ (fun τ => (y * I) * -b τ) x' =
        X.flow ξ (fun τ => (((y * I : ℂ) * -b τ).re : ℂ) + b τ) x := by
      rw [hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]
      congr 1
      congr 1
      funext τ
      exact Complex.ext (by simp) (by rw [hs]; simp)
    rw [he]
    exact h
  have key := half_plane_bound (g := fun z => P (X.flow ξ (fun τ => z * -b τ) x'))
    (hP.1.comp (differentiable_flow X ξ (fun τ => -b τ) x').differentiableOn fun z hz =>
      FjCauchy.flow_mem_dom X hξ hx' _ fun τ =>
        add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx' τ) (him z hz τ))
    (fun z hz => norm_flow_le X hP hF hξ hx' _ (him z hz)) hreal
  have he : X.flow ξ (fun τ => 1 * -b τ) x' = x := by
    rw [hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]
    have : ((fun τ => 1 * -b τ) + b) = 0 := by funext τ; simp
    rw [this, EmbeddingHermitianPairs.flow_zero]
  simp only [he] at key
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans key
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hn'))
  have hr := (m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx b hx').2
  have hr2 : X.nfac la x / X.nfac la x' ≤ ∏ τ, q τ ^ (-w) := by
    refine le_trans hr (Finset.prod_le_prod₀ (fun τ _ => ?_) fun τ _ => ?_)
    all_goals
      have hqq : 1 + (b τ).im / X.ttV (X.embV ξ) x τ = q τ := by
        change 1 + (b τ).im / X.tt ξ x τ = q τ
        rw [hbim, mul_div_assoc, div_self (ht τ).ne']; ring
      have h1 : 1 ≤ (q τ)⁻¹ := (one_le_inv₀ (hq τ).1).mpr (hq τ).2
      simp only [hqq, max_eq_right ((hq τ).2.trans h1)]
    · positivity
    · rw [Real.rpow_neg (hq τ).1.le, ← Real.inv_rpow (hq τ).1.le]
      exact Real.rpow_le_rpow_of_exponent_le h1 (hw τ)
  calc X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
    _ ≤ B / X.nfac la x' * X.nfac la x := mul_le_mul_of_nonneg_right key hn.le
    _ = B * (X.nfac la x / X.nfac la x') := by ring
    _ ≤ B * ∏ τ, q τ ^ (-w) := mul_le_mul_of_nonneg_left hr2 hB0

end GlobalTheory.CuspStep
end

section

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
open scoped ComplexConjugate

namespace GlobalTheory.CuspFrom.FlowMaj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma majForm_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ w u = conj (X.Hf x τ u w) := by
  rw [X.Hf_eq_jp, X.Hf_eq_jp, hermC_conj τ.1 X.Gm_herm, X.hermC_jp_left hx]

lemma majForm_sub_smul (x : Frame X.Ψ r) (τ : X.Ψ) (a : ℂ) (v e w : Fin r → ℂ) :
    X.Hf x τ (v - a • e) w = X.Hf x τ v w - a * X.Hf x τ e w := by
  simp only [X.Hf_eq_jp, X.jp_sub, X.jp_smul, hermC_sub_left, hermC_smul_left]

lemma maj_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  have h := X.Hf_self hx τ 0
  rw [X.Hf_eq_jp, hermC_zero_right] at h
  exact_mod_cast h.symm

lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X hx]
  · exact (X.maj_pos hx τ hv).le

lemma maj_split {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : ℂ) (e u : Fin r → ℂ)
    (h : X.Hf x τ u e = 0) : X.maj x τ (u + a • e) = X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e := by
  have h' : X.Hf x τ e u = 0 := by rw [majForm_conj X hx, h, map_zero]
  have h1 := X.Hf_self hx τ (u + a • e)
  have h2 := X.Hf_self hx τ u
  have h3 := X.Hf_self hx τ e
  simp only [X.Hf_eq_jp] at h h' h1 h2 h3
  simp only [X.jp_add, X.jp_smul, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right,
    h, h', h2, h3] at h1
  have h4 : a * conj a = ((‖a‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' a
  have h5 : ((X.maj x τ (u + a • e) : ℝ) : ℂ) = ((X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e : ℝ) : ℂ) := by
    rw [← h1]
    push_cast
    linear_combination (X.maj x τ e : ℂ) * h4
  exact_mod_cast h5

lemma majForm_perp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) {e : Fin r → ℂ} (he : e ≠ 0) :
    X.Hf x τ (v - (X.Hf x τ v e / X.Hf x τ e e) • e) e = 0 := by
  have h0 : X.Hf x τ e e ≠ 0 := by
    rw [X.Hf_self hx]
    exact_mod_cast (X.maj_pos hx τ he).ne'
  rw [majForm_sub_smul, div_mul_cancel₀ _ h0, sub_self]

lemma majForm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  by_cases hw : w = 0
  · rw [hw, maj_zero X hx, X.Hf_eq_jp, hermC_zero_right]
    simp
  have hp := X.maj_pos hx τ hw
  have h1 := maj_split X hx τ (X.Hf x τ v w / X.Hf x τ w w) w _ (majForm_perp X hx τ v hw)
  rw [sub_add_cancel] at h1
  have h2 := maj_nonneg X hx τ (v - (X.Hf x τ v w / X.Hf x τ w w) • w)
  have h3 : ‖X.Hf x τ v w / X.Hf x τ w w‖ ^ 2 * X.maj x τ w * X.maj x τ w = ‖X.Hf x τ v w‖ ^ 2 := by
    rw [norm_div, X.Hf_self hx τ w, Complex.norm_real, Real.norm_of_nonneg hp.le]
    field_simp
  rw [← h3]
  exact mul_le_mul_of_nonneg_right (by linarith) hp.le

lemma maj_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  have h1 := X.Hf_self hx τ (X.jp x τ v)
  have h2 := X.Hf_self hx τ v
  rw [X.Hf_eq_jp, X.hermC_jp_jp hx, ← X.Hf_eq_jp, h2] at h1
  exact_mod_cast h1.symm

lemma herm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  have h := majForm_cs X hx τ (X.jp x τ v) w
  rwa [X.Hf_eq_jp, X.jp_jp hx, maj_jp X hx] at h

lemma maj_flow {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ)
    (hxs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) :
    X.maj (X.flow ξ s x) τ v = X.maj x τ v +
      ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
        (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ)) := by
  have hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [← emb_herm, hξ.2.1, map_zero]
  have he : Data.emb τ.1 ξ ≠ 0 := emb_ne_zero τ.1 hξ.2.2
  have hH := majForm_perp X hx τ v he
  set a := X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with ha
  set u := v - a • Data.emb τ.1 ξ with hu
  have hu0 : hermC τ.1 X.Gm u (Data.emb τ.1 ξ) = 0 := by
    rw [hu, hermC_sub_left, hermC_smul_left, hv, hiso, mul_zero, sub_zero]
  have hp : hermC τ.1 X.Gm (X.ppos x τ u) (Data.emb τ.1 ξ) = 0 := by
    have h := hH
    rw [X.Hf_eq_two_ppos, hu0, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  have hpp := Data.ppos_flow X ξ τ hx s hxs u hu0 hp
  have hHy : ∀ w, X.Hf (X.flow ξ s x) τ u w = X.Hf x τ u w := fun w => by
    rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hpp]
  have hm : X.maj (X.flow ξ s x) τ u = X.maj x τ u := by
    have h := hHy u
    rw [X.Hf_self hxs, X.Hf_self hx] at h
    exact_mod_cast h
  have h1 := maj_split X hx τ a _ u hH
  have h2 := maj_split X hxs τ a _ u ((hHy _).trans hH)
  rw [hu, sub_add_cancel, ← hu] at h1 h2
  rw [h1, h2, hm]
  ring

end GlobalTheory.CuspFrom.FlowMaj

namespace GlobalTheory.CuspFrom

theorem flowMajSt_holds : FlowMajSt := fun _ _ _ _ _ X =>
  ⟨fun _ hξ _ hx s hxs τ v hv => FlowMaj.maj_flow X hξ hx s hxs τ v hv,
    fun _ hx τ v w => ⟨FlowMaj.herm_cs X hx τ v w, FlowMaj.majForm_cs X hx τ v w⟩⟩

end GlobalTheory.CuspFrom
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem spMap_fromSpec_mem_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [Field K]
    (ψ : Γ(X, U) →+* K) (p : Γ(X, U)) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ X.basicOpen p ↔ ψ p ≠ 0 := by
  have h : spMap ψ s ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen p ↔ ψ p ≠ 0 := by
    rw [hU.fromSpec_preimage_basicOpen]
    change ψ p ∉ (show PrimeSpectrum K from s).asIdeal ↔ _
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from s).asIdeal, Ideal.mem_bot]
  exact h

theorem spMap_fromSpec_mem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [CommRing K]
    (ψ : Γ(X, U) →+* K) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ U := by
  have h : hU.fromSpec (spMap ψ s) ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨_, rfl⟩
  exact h

end GlobalTheory.ShFam.BdArc
end
end
