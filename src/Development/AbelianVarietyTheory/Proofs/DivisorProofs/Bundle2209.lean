module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle065
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.CM.IntCoord
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.HomIndep

theorem phiP_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (x : Fin p → 𝓞 E),
    ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) = 1 → x = 0 := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X x hx
  classical
  have hU := GlobalTheory.thetaUnifAV_all
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨τ, hτ⟩ := GlobalTheory.CM.NumInh.exists_char X.split X.ρ_sq
  have FA : ∀ b, GenFib (X.A b).pol := fun b =>
    (GenFib.nonempty_of_baseChange hL.polBaseChange K (X.A b).pol).some
  have FB : GenFib X.B.pol := (GenFib.nonempty_of_baseChange hL.polBaseChange K X.B.pol).some
  have hMex : ∀ j : Fin p ⊕ Fin q, ∃ M, (FA j.isLeft).IsDiffOf FB (X.φ j) M := fun j =>
    ((GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K _ (FA j.isLeft) _ FB (X.φ j) (X.lin j).isMonHom).1).exists
  choose M hM using hMex
  obtain ⟨-, hrank, hinj, hind, -⟩ := GlobalTheory.CM.Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  funext a
  show x a = 0
  have hcA := integral_tangent_coordinates K _ (FA true)
  have hcB := integral_tangent_coordinates K _ FB

  have hne : (FA true).eigLat (X.A true).t.act τ ≠ ⊥ := by
    intro h0
    have h1 := hrank (Sum.inl a, τ)
    rw [if_pos (by simpa using hτ)] at h1
    change latRank K (((FA true).eigLat (X.A true).t.act τ).map ((M (Sum.inl a)).restrictScalars (𝓞 K))) = 1 at h1
    rw [h0] at h1
    have hb : Submodule.span K (((⊥ : Submodule (𝓞 K) (Fin (FA true).P₀.g → K)).map
        ((M (Sum.inl a)).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin FB.P₀.g → K)) : Set (Fin FB.P₀.g → K)) = ⊥ :=
      Submodule.span_eq_bot.2 fun z hz => by
        obtain ⟨y, hy, rfl⟩ := hz
        obtain rfl : y = 0 := (Submodule.mem_bot (𝓞 K)).1 hy
        exact map_zero _
    rw [latRank, hb, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have hs : ∀ b, FB.IsCoord (u ≫ ((X.A true).t.act.act (x b) ≫ phiP X b)) (M (Sum.inl b) (τ (x b) • e)) := by
    intro b
    rw [← Category.assoc]
    exact hM (Sum.inl b) _ _ (isCoord_smul (FA true) hu (heig (x b)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ b ∈ s, ((X.A true).t.act.act (x b) ≫ phiP X b))
      (∑ b ∈ s, M (Sum.inl b) (τ (x b) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert b s hb ih =>
      rw [Finset.prod_insert hb, Finset.sum_insert hb, comp_mul]
      exact isCoord_mul FB (hs b) ih
  have hsum : ∑ b, M (Sum.inl b) (τ (x b) • e) = 0 := by
    have h1 := hprod Finset.univ
    rw [hx, comp_one] at h1
    exact (hcB.1 _ h1.1).unique h1 (isCoord_one FB)
  have hind' := hind.comp (f := fun b : Fin p => ((Sum.inl b, τ) : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K)))
    (fun b b' h => Sum.inl_injective (Prod.ext_iff.1 h).1)
  have hva := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind' Finset.univ
    (fun b => M (Sum.inl b) (τ (x b) • e))
    (fun b _ => Submodule.subset_span (Submodule.mem_map_of_mem
      (f := (M (Sum.inl b)).restrictScalars (𝓞 K)) (Submodule.smul_mem _ (τ (x b)) he))) hsum a (Finset.mem_univ a)
  have h0 : τ (x a) • e = 0 := hinj (Sum.inl a) (by rw [hva]; exact (map_zero _).symm)
  rw [← algebraMap_smul K (τ (x a)) e, smul_eq_zero] at h0
  have hτa : τ (x a) = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 (h0.resolve_right he0)
  exact _root_.GlobalTheory.CM.ringOfIntegers_hom_injective τ (by rw [hτa, map_zero])

end GlobalTheory.FlatCM.HomIndep

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

section General

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]

theorem finrank_eq_two_mul_nPl : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := by
  rw [IsTotallyComplex.finrank, Formalism.HN.nPl, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem rkK_mul_muDef [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG)
    (hr : Formalism.HN.rkK L ≠ 0) :
    (Formalism.HN.rkK L : ℝ) * (Formalism.HN.muDef b X L / 2) = -Real.log (Formalism.HN.ht b X L) / (2 * (Formalism.HN.nPl K : ℝ)) := by
  obtain ⟨-, hrk, hht⟩ := Formalism.HN.plLat K V ι b X hX L hL
  have hd : (0 : ℝ) < |(NumberField.discr K : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hj : (0 : ℝ) < (Formalism.HN.rkK L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have e₁ : Formalism.HN.ht b X L = (2 : ℝ) ^ (Formalism.HN.nPl K * Formalism.HN.rkK L) *
      |(NumberField.discr K : ℝ)| ^ (-(Formalism.HN.rkK L : ℝ) / 2) *
      Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) := rfl
  have hC : 0 < Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    rw [e₁] at hht
    exact pos_of_mul_pos_right hht (by positivity)
  have hlog : Real.log (Formalism.HN.ht b X L) = ((Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L) * Real.log 2 +
      (-(Formalism.HN.rkK L : ℝ) / 2) * Real.log |(NumberField.discr K : ℝ)| +
      Real.log (Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)) := by
    rw [e₁, Real.log_mul (by positivity) hC.ne', Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow hd]
    push_cast; ring
  have hrk' : (Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) : ℝ) =
      2 * (Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L := by
    have : Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) = Module.finrank ℚ K * Formalism.HN.rkK L := hrk
    rw [this, finrank_eq_two_mul_nPl]; push_cast; ring
  have hmu : Formalism.HN.muDef b X L = 2 * (-Real.log (Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)) /
      (2 * (Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L)) - Real.log 2 +
      Real.log |(NumberField.discr K : ℝ)| / (2 * (Formalism.HN.nPl K : ℝ)) := by
    rw [Formalism.HN.muDef, Formalism.HN.slope, Formalism.F.slope, Formalism.F.deg, hrk', Formalism.HN.logDisc, finrank_eq_two_mul_nPl]
    push_cast; ring
  rw [hmu, hlog]
  field_simp
  ring

theorem pgeoDeg_eq_deg {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V) (hinv : h.IsConjInv) {N : (K →+* ℂ) → V → ℝ} (hN : ∀ σ x, h.nrm σ x = N σ x)
    (hg : AllWt.HasGram N) {L : Submodule (𝓞 K) V} (hL : L.FG) : ReciprocityTheory.GeometryOfNumbersTheory.deg h L = AllWt.deg N L := by
  by_cases h0 : L = ⊥
  · subst h0
    have hv : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K (⊥ : Submodule (𝓞 K) V) (Fin.elim0 : Fin 0 → V) :=
      ⟨fun i => i.elim0, linearIndependent_empty_type, by simp⟩
    rw [AllWt.deg_bot, ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hL hv]
    simp [ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily, ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram]
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hG⟩ := hg.some
  haveI : FiniteDimensional K V := Module.Basis.finiteDimensional_of_finite b
  have hr : Formalism.HN.rkK L ≠ 0 := by
    intro hr
    apply h0
    rw [Formalism.HN.rkK, Submodule.finrank_eq_zero] at hr
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Submodule.span K (L : Set V) := Submodule.subset_span hx
    rw [hr, Submodule.mem_bot] at hx'
    rw [hx']
    exact zero_mem _
  rw [GlobalTheory.T.hermitian_lattice_degree_eq_neg_log_frame_height K V h hinv (Fin n) b X (fun v => (hG v).1) (fun v x => ((hG v).2 x).trans (hN _ x).symm) L hL,
    AllWt.deg, AllWt.slope, AllWt.slope_sq_eq hG hL, rkK_mul_muDef b X (fun v => (hG v).1) hL hr]

end General

theorem isTotallyComplex_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) : IsTotallyComplex c.F :=
  ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

theorem Ready.degM_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, (h.data f₁ f₂ th k).degM j = GlobalTheory.AllWt.degOn U x V dict Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0) := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k j hj
  haveI : IsTotallyComplex c.F := isTotallyComplex_coeff c
  have hM : (h.data f₁ f₂ th k).M j = (GlobalTheory.AllWt.latOn U Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0)).map
      ((h.equivV f₁ f₂ th k hj).toLinearMap.restrictScalars (𝓞 c.F)) := by
    ext y
    constructor
    · intro hy
      refine ⟨(h.equivV f₁ f₂ th k hj).symm y, ?_, (h.equivV f₁ f₂ th k hj).apply_symm_apply y⟩
      refine (h.equivV_mem f₁ f₂ th k hj _).1 ?_
      rw [LinearEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨g, hg, rfl⟩
      exact (h.equivV_mem f₁ f₂ th k hj g).2 hg
  rw [HilbertSamuel.Data.degM, hM, ← FibIndep.deg_map_of_isometry
    (HermTools.comap ((h.data f₁ f₂ th k).nm j) (h.equivV f₁ f₂ th k hj).toLinearMap
      (h.equivV f₁ f₂ th k hj).injective) _ (h.equivV f₁ f₂ th k hj).toLinearMap (fun _ _ _ => rfl)
    (h.good j hj).2.1]
  exact pgeoDeg_eq_deg _ (HermTools.isConjInv_comap ((h.data f₁ f₂ th k).conjInv j) _ _)
    (fun σ x => h.nrm_equivV f₁ f₂ th k hj σ x) (h.good j hj).1 (h.good j hj).2.1

end GlobalTheory.CompHS
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem GlobalTheory.HorFrame.exists_deform_of_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁) (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ {ι : Type} [Fintype ι] (d : ι → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → ∀ (Mx : ι → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →+* K) (hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K), X.F.ChartFr k _ hk Q → ∀ (θ : Γ(M.X, W₁) →+* DualNumber K) (m : ι → K), (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * ψ (d a s).snd) → ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (∑ a, m a • (ψ ∘ Mx a)) ∧ spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hk₁ _ Q₀ hQ₀ ι _ d hd Mx hMx K _ _ ψ hk Q hQ θ m hθ1 hθ2
  haveI := c.fin
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] (f g : A →+* B), spMap f = spMap g → f = g := by
    intro A B _ _ f g h
    have := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom this
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hjs : ∀ {T : Type} [CommRing T] [Algebra c.F T] (P : FrPt Xo c T),
      frX P ≫ Y.j ≫ Y.s = spMap (algebraMap c.F T) := by
    intro T _ _ P
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, frX_snd,
      hid, Category.comp_id]
  have e1 : frX Q ≫ Y.j = spMap ψ ≫ frX Q₀ ≫ Y.j := by
    rw [hQ.over, hQ₀.over]; simp only [Category.assoc]
  have hψα : ψ.comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F K := by
    have h2 := congrArg (· ≫ Y.s) e1
    simp only [Category.assoc] at h2
    rw [hjs Q, hjs Q₀, spMap_comp'] at h2
    exact (hinj _ _ h2).symm

  let ψA : Γ(M.X, W₁) →ₐ[c.F] K := ⟨ψ, fun r => RingHom.congr_fun hψα r⟩
  have hfrX : frX Q = spMap ψ ≫ frX Q₀ := by
    refine xF_ext (Y := Y) (frX_snd Q) ?_ (by rw [e1, Category.assoc])
    rw [Category.assoc, frX_snd, spMap_comp', hψα]
  have hQx : Q.x = spMap ψ ≫ Q₀.x := by
    rw [← frX_fst, hfrX, Category.assoc, frX_fst]
  have hFQ : FrMap ψA Q₀ Q := by
    obtain ⟨Q', hQ'⟩ := exists_frMap ψA Q₀
    have hc := hQ₀.frMap hQ' (z' := (spMap ψ ≫ tau hW₁) ≫ toFlag M) (by simp only [Category.assoc]) hk
    rwa [hc.unique hQ] at hQ'

  have hdu : ∀ φ : Γ(M.X, W₁) →+* DualNumber K, (∀ s, (φ s).fst = ψ s) →
      φ.comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber K) := by
    intro φ hφ
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · rw [RingHom.comp_apply, hφ, ← RingHom.comp_apply, hψα]; simp [TrivSqZeroExt.algebraMap_eq_inl']
    · rw [GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero c.F (φ.comp (algebraMap c.F _)) a]; simp [TrivSqZeroExt.algebraMap_eq_inl']
  let θA : Γ(M.X, W₁) →ₐ[c.F] DualNumber K := ⟨θ, fun r => RingHom.congr_fun (hdu θ hθ1) r⟩
  obtain ⟨w, hw⟩ := exists_frMap θA Q₀
  have hwc : X.F.ChartFr k (spMap θ ≫ tau hW₁ ≫ toFlag M) (le_preimage_comp _ hk₁) w :=
    hQ₀.frMap hw rfl _
  have hwpt : spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := FlagCover.eq_ptY hwc.lies
  have hwx : w.x = spMap θ ≫ Q₀.x := by
    rw [← frX_fst, ← frX_frMap hw, Category.assoc, frX_fst]
  have hred : (GlobalTheory.FlagTan.red c K).toRingHom.comp θ = ψ := RingHom.ext fun s => hθ1 s
  have hdef : IsDef Q w := by
    obtain ⟨Q', hQ'⟩ := exists_frMap (GlobalTheory.FlagTan.red c K) w
    have hc := hwc.frMap hQ' (z' := (spMap ψ ≫ tau hW₁) ≫ toFlag M)
      (by rw [← Category.assoc, spMap_comp', hred]; simp only [Category.assoc]) hk
    show FrMap _ w Q
    rwa [hc.unique hQ] at hQ'

  have hθc1 : ∀ a s, (((dualMap ψ).comp (d a)) s).fst = ψ s := by
    intro a s; simp [dualMap, hd]
  have hTan : ∀ φ : Γ(M.X, W₁) →+* DualNumber K, (∀ s, (φ s).fst = ψ s) →
      GlobalTheory.FlagTan.IsTanX Q (spMap φ ≫ Q₀.x) := by
    intro φ hφ
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Q₀.x_over]
      unfold sOf
      rw [spMap_comp', ← RingHom.comp_assoc, hdu φ hφ]
    · rw [← Category.assoc, spMap_comp', hQx]
      have : (GlobalTheory.FlagTan.red c K).toRingHom.comp φ = ψ := RingHom.ext fun s => hφ s
      rw [this]
  have hKSa : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) Q (spMap ((dualMap ψ).comp (d a)) ≫ Q₀.x) (ψ ∘ Mx a) := by
    intro a
    have := hMx a K ψA Q hFQ
    rwa [← Category.assoc, spMap_comp'] at this
  refine ⟨w, hdef, ?_, hwpt⟩
  rw [hwx]
  refine GlobalTheory.T.kodaira_spencer_tangent_vectors_lift (hKS K Q) (x := fun a => spMap ((dualMap ψ).comp (d a)) ≫ Q₀.x)
    (fun a => hTan _ (hθc1 a)) hKSa (hTan θ hθ1) m ?_
  intro O f h' hc
  exact GlobalTheory.T.evalRingPoint_dualNumber_snd_linear_derivation Q₀.x ψ (fun a => (dualMap ψ).comp (d a)) θ m hθc1 hθ1
    (fun s => by rw [hθ2 s]; simp [dualMap]) O f h' hc
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

noncomputable section

open IsDedekindDomain
namespace GlobalTheory.CompatLim

theorem norm_sub_le_of_dvd (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (x y : ℤ) (h : ((ℓ ^ k : ℕ) : ℤ) ∣ x - y) :
    ‖((x : ℤ_[ℓ]) - (y : ℤ_[ℓ]))‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : ℤ_[ℓ]), ?_⟩
  have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hc
  push_cast at this
  rw [← this]

theorem exists_padicInt_lim (p ℓ : ℕ) [Fact ℓ.Prime] (hp : p.Prime) (hne : ℓ ≠ p) (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) :
    ∃ L : ℤ_[ℓ], ∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : ℤ_[ℓ], L = (a n : ℤ_[ℓ]) + (n : ℤ_[ℓ]) * b := by
  have hℓ : ℓ.Prime := Fact.out
  have hcop : ∀ k, (ℓ ^ k).Coprime p := fun k => Nat.Coprime.pow_left k ((Nat.coprime_primes hℓ hp).2 hne)
  have hpos : ∀ k, 0 < ℓ ^ k := fun k => pow_pos hℓ.pos k

  have key : ∀ k m, k ≤ m → ((ℓ ^ k : ℕ) : ℤ) ∣ a (ℓ ^ m) - a (ℓ ^ k) := by
    intro k m hkm
    have h := ha (ℓ ^ k) (ℓ ^ (m - k)) (hpos k) (hpos _) (by rw [← pow_add, Nat.add_sub_cancel' hkm]; exact hcop m)
    rwa [← pow_add, Nat.add_sub_cancel' hkm] at h
  set s : ℕ → ℤ_[ℓ] := fun k => (a (ℓ ^ k) : ℤ_[ℓ]) with hs
  have hdist : ∀ k m, k ≤ m → dist (s m) (s k) ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    rw [dist_eq_norm]
    exact norm_sub_le_of_dvd ℓ k _ _ (key k m hkm)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hcs : CauchySeq s := by
    refine cauchySeq_of_le_geometric ((ℓ : ℝ)⁻¹) 1 (inv_lt_one_of_one_lt₀ hℓ1) fun k => ?_
    rw [dist_comm, _root_.one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdist k (k + 1) (Nat.le_succ k)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLk : ∀ k, ‖L - s k‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have hmem : L ∈ Metric.closedBall (s k) ((ℓ : ℝ) ^ (-(k : ℤ))) :=
      Metric.isClosed_closedBall.mem_of_tendsto hL
        (Filter.eventually_atTop.2 ⟨k, fun m hm => Metric.mem_closedBall.2 (hdist k m hm)⟩)
    rwa [Metric.mem_closedBall, dist_eq_norm] at hmem
  refine ⟨L, fun n hn hnp => ?_⟩
  set e := n.factorization ℓ
  set m := n / ℓ ^ e
  have hnm : ℓ ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hm : ℓ.Coprime m := Nat.coprime_ordCompl hℓ hn.ne'
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hnm; omega

  have h1 : L - s e ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ e} := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (hLk e)

  have h2 := ha (ℓ ^ e) m (hpos e) hmpos (by rw [hnm]; exact hnp)
  rw [hnm] at h2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h1
  obtain ⟨d, hd⟩ := h2
  have hu : IsUnit (m : ℤ_[ℓ]) := PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hm)
  obtain ⟨u, hu⟩ := hu
  refine ⟨(u⁻¹ : ℤ_[ℓ]ˣ) * (c - (d : ℤ_[ℓ])), ?_⟩
  have hd' : (a n : ℤ_[ℓ]) - s e = (ℓ : ℤ_[ℓ]) ^ e * d := by
    have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hd
    push_cast at this
    simpa [hs] using this
  have hn' : (n : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ e * u := by
    rw [hu, ← hnm]; push_cast; ring
  rw [hn']
  have : (ℓ : ℤ_[ℓ]) ^ e * (u : ℤ_[ℓ]) * ((u⁻¹ : ℤ_[ℓ]ˣ) * (c - d)) = (ℓ : ℤ_[ℓ]) ^ e * (c - d) := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc (u : ℤ_[ℓ]), Units.mul_inv, _root_.one_mul]
  rw [this]
  linear_combination hc - hd'

open Rat.HeightOneSpectrum in
theorem natGenerator_ne (p : ℕ) (v : AwayP p) : (primesEquiv v.1 : ℕ) ≠ p := by
  obtain ⟨w, hw⟩ := v
  intro h
  apply hw
  have hs := span_natGenerator (R := ℤ) w
  change natGenerator w = p at h
  rw [h] at hs
  rw [hs]
  ext x
  rw [Ideal.mem_map_of_equiv]
  simp [eq_intCast]


open Rat.HeightOneSpectrum in
theorem exists_integer_lim (p : ℕ) [hp : Fact p.Prime] (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) (v : AwayP p) :
    ∃ x : v.1.adicCompletionIntegers ℚ, ∀ n : ℕ, 0 < n → n.Coprime p →
      ∃ b : v.1.adicCompletionIntegers ℚ, x = (a n : v.1.adicCompletionIntegers ℚ) + (n : v.1.adicCompletionIntegers ℚ) * b := by
  haveI : Fact (primesEquiv v.1 : ℕ).Prime := ⟨(primesEquiv v.1).2⟩
  obtain ⟨L, hL⟩ := exists_padicInt_lim p (primesEquiv v.1 : ℕ) hp.out (natGenerator_ne p v) a ha
  let e := (RingEquivClass.toRingEquiv (adicCompletionIntegers.padicIntEquiv (R := ℤ) v.1)).symm
  refine ⟨e L, fun n hn hnp => ?_⟩
  obtain ⟨b, hb⟩ := hL n hn hnp
  refine ⟨e b, ?_⟩
  rw [hb, map_add (f := _), map_mul, map_intCast, map_natCast]

theorem exists_lim : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) → ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := by
  intro p _ a ha
  choose x hx using exists_integer_lim p a ha
  let α : AfP p := RestrictedProduct.mk (fun v => (x v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (x v).2)
  refine ⟨α, fun v => (x v).2, fun n hn hnp => ?_⟩
  choose b hb using fun v => hx v n hn hnp
  let β : AfP p := RestrictedProduct.mk (fun v => (b v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (b v).2)
  refine ⟨β, fun v => (b v).2, ?_⟩
  apply RestrictedProduct.ext
  intro v
  have h1 : AfP.eval v α = x v := rfl
  have h2 : AfP.eval v β = b v := rfl
  have h3 : AfP.eval v ((a n : AfP p) + n • β) = (a n : v.1.adicCompletion ℚ) + (n : v.1.adicCompletion ℚ) * b v := by
    rw [map_add (f := _), map_intCast, map_nsmul, h2, nsmul_eq_mul]
  change AfP.eval v α = AfP.eval v ((a n : AfP p) + n • β)
  rw [h3, h1, hb v]
  push_cast
  rfl

end GlobalTheory.CompatLim
end
end
