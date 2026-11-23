module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.WeilBound.CoreStatements.ProjectiveValuations.ExistsChartFrBor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.WeilBound.CoreStatements.ProjectiveValuations.OpenImmersionCompStructureEqGeneric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle641
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Limits

namespace DifferentiableLines.CellsProj

private theorem pt_str {R A : Type} [CommRing R] [CommRing A] {N : ℕ}
    (c : R →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) :
    GlobalTheory.ProjSpace.pt c v hv ≫ PSpace.str R N = spMap c := by
  rw [GlobalTheory.ProjSpace.pt, PSpace.str, GlobalTheory.ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r

theorem isProper_of_proj {K : Type} [CommRing K] {P : Scheme.{0}} {t : P ⟶ Sp K} (h : IsProjOver t) : IsProper t := by
  obtain ⟨N, j, _, e⟩ := h
  have := isProper_str K N
  rw [← e]
  infer_instance

theorem exists_joint {K : Type} [CommRing K] {X Z : Scheme.{0}} (s : X ⟶ Sp K) (hs : IsProjOver s) (π : Z ⟶ X)
    {I : Type} (n : I → ℕ) (g : ∀ i, Z ⟶ PSpace K (n i)) (hg : ∀ i, g i ≫ PSpace.str K (n i) = π ≫ s)
    (T : Finset I) : ∃ (P : Scheme.{0}) (t : P ⟶ Sp K) (q : Z ⟶ P), IsProjOver t ∧ q ≫ t = π ≫ s ∧
      ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ q = a' ≫ q → a ≫ π = a' ≫ π ∧ ∀ i ∈ T, a ≫ g i = a' ≫ g i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨X, s, π, hs, rfl, fun W a a' h => ⟨h, by simp⟩⟩
  | insert i T _ ih =>
    obtain ⟨P, t, q, ht, hq, H⟩ := ih
    have hi : IsProjOver (PSpace.str K (n i)) := ⟨n i, 𝟙 _, inferInstance, Category.id_comp _⟩
    refine ⟨pullback t (PSpace.str K (n i)), pullback.fst _ _ ≫ t, pullback.lift q (g i) (hq.trans (hg i).symm),
      GlobalTheory.ProjSpace.isProjOver_pullback ht hi, by rw [pullback.lift_fst_assoc, hq], fun W a a' h => ?_⟩
    have h1 := congrArg (· ≫ pullback.fst _ _) h
    have h2 := congrArg (· ≫ pullback.snd _ _) h
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at h1 h2
    refine ⟨(H W a a' h1).1, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact h2
    · exact (H W a a' h1).2 j hj

theorem isProjOver_of_joint {K : Type} [CommRing K] {X Z : Scheme.{0}} (s : X ⟶ Sp K) (hs : IsProjOver s) (π : Z ⟶ X)
    [IsProper π] {I : Type} [Finite I] (n : I → ℕ) (g : ∀ i, Z ⟶ PSpace K (n i))
    (hg : ∀ i, g i ≫ PSpace.str K (n i) = π ≫ s)
    (ext : ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ i, a ≫ g i = a' ≫ g i) → a = a') :
    IsProjOver (π ≫ s) := by
  have := Fintype.ofFinite I
  obtain ⟨P, t, q, ht, hq, H⟩ := exists_joint s hs π n g hg Finset.univ
  have := isProper_of_proj ht
  have := isProper_of_proj hs
  have : IsProper (q ≫ t) := by rw [hq]; infer_instance
  have hp : IsProper q := IsProper.of_comp q t
  have hm : Mono q := ⟨fun a a' h => ext _ a a' (H _ a a' h).1 fun i => (H _ a a' h).2 i (Finset.mem_univ i)⟩
  have : IsClosedImmersion q := (IsClosedImmersion.iff_isProper_and_mono q).2 ⟨hp, hm⟩
  rw [← hq]
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion q ht

theorem smooth_C (R σ : Type) [CommRing R] [Finite σ] :
    SmoothOfRelativeDimension (Nat.card σ) (spMap (MvPolynomial.C : R →+* MvPolynomial σ R)) := by
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card σ))).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (GlobalTheory.Adelic.isStandardSmooth_mvPolynomial R σ)

theorem smooth_cell {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (σ : Type) [Finite σ] :
    SmoothOfRelativeDimension (Nat.card σ + 0)
      (spMap (MvPolynomial.C : Γ(X, U) →+* MvPolynomial σ Γ(X, U)) ≫ hU.fromSpec) :=
  @smoothOfRelativeDimension_comp _ _ _ _ _ _ hU.fromSpec (smooth_C Γ(X, U) σ) inferInstance

end DifferentiableLines.CellsProj


open DifferentiableLines.CellsProj GlobalTheory.FlagEmb GlobalTheory.FlagMod in
theorem DifferentiableLines.flag_embedding_atlas_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, Z ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ Z)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∃ d : ℕ, SmoothOfRelativeDimension d (π ≫ Y.s) ∧ IsProjOver (π ≫ Y.s) := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ hκ hZ hs
  let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers (A.B × Pm Dw.mult) (fun k => Sp (CR Dw.mult (A.V k.1)))
    (fun k => κ k.1 k.2) (fun z => by
      obtain ⟨b, w, y, h⟩ := hZ.cover z
      exact ⟨(b, w), y, h⟩) (fun k => hκ k.1 k.2)
  refine ⟨Nat.card (CellVar Dw.mult) + 0 + Dw.dim, ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension.{0} (Nat.card (CellVar Dw.mult) + 0 + Dw.dim))
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (Nat.card (CellVar Dw.mult) + 0 + Dw.dim)))
    refine IsZariskiLocalAtSource.of_openCover
      (P := @SmoothOfRelativeDimension.{0} (Nat.card (CellVar Dw.mult) + 0 + Dw.dim)) 𝒰 fun k => ?_
    change SmoothOfRelativeDimension _ (κ k.1 k.2 ≫ π ≫ Y.s)
    rw [← Category.assoc, hZ.plk.base, cbase]
    exact @smoothOfRelativeDimension_comp _ _ _ _ _ _ Y.s (smooth_cell (A.V k.1).2 (CellVar Dw.mult)) hs
  · have := hZ.proper
    refine isProjOver_of_joint Y.s Y.proj π (fun en : En Dw.mult => plN A.N en.1) g (fun en => ?_) hZ.ext
    refine 𝒰.hom_ext _ _ fun k => ?_
    change κ k.1 k.2 ≫ g en ≫ _ = κ k.1 k.2 ≫ π ≫ Y.s
    obtain ⟨hu, e⟩ := hZ.plk.plk k.1 k.2 en
    rw [← Category.assoc, e, pt_str, ← Category.assoc, hZ.plk.base, cbase, Category.assoc]
    have h : (A.V k.1).2.fromSpec ≫ Y.s = spMap ((A.alpha k.1).comp (RingHom.id c.F)) :=
      (spMap_ev_top _).symm
    rw [h]
    exact Spec.map_comp _ _
end

section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory


open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions MonObj GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop GlobalTheory.HSApp in
theorem exists_frBor_of_matches (T : TorFlag Xo c) {A : Type} [CommRing A] (q : Sp A ⟶ T.X.YY) (k : T.X.F.J)
    (hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U k) {φ : c.F →+* A} {x : Sp A ⟶ gen T.Y} (hx : q ≫ T.X.π = x ≫ genι T.Y)
    (fr : EigFrame T.Y φ (x ≫ genι T.Y))
    (hfr : ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k q hz hx τ j)).left) (ψ : A →+* CAt σ)
    {y : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y) {z : Sp (CAt σ) ⟶ T.X.YY}
    (e : spMap ψ ≫ q = z) (hz' : ⊤ ≤ z ⁻¹ᵁ T.X.F.U k) :
    ∃ (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ), T.X.F.ChartFr k z hz' Q ∧ FrBor t Q y ∧ ∀ s, t (some s) = 1 := by
  subst e
  let z' : Sp (CAt σ) ⟶ T.X.YY := spMap ψ ≫ q
  have ex : spMap ψ ≫ (x ≫ genι T.Y) = z' ≫ T.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ T.Y.j = z' ≫ T.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ T.Y.j = (GlobalTheory.AllWt.ptF y ≫ T.Y.jQ) ≫ genι T.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ ≫ (x ≫ genι T.Y) := (congrArg (· ≫ genι T.Y) hm.1).trans (Category.assoc _ _ _)
    _ = z' ≫ T.X.π := ex
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec T.Y y hxy τ j = GlobalTheory.FlagMod.frVec T.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← T.X.F.tanPull_vecAt k ψ q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := T.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := GlobalTheory.CompHS.BridgeValue.exists_gen_unit Q y eQ
  let t : Ix D → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  refine ⟨Q, t, hQ, GlobalTheory.FlagMod.frBor_of_frVec (T.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => ?_) (fun _ => hu0), fun _ => rfl⟩
  rw [hv τ j]
  refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j' j • _ = 0
    rw [Matrix.one_apply_ne hj', zero_smul]
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j j • _ = _
    rw [Matrix.one_apply_eq, one_smul]

theorem matches_of_sameLie {Z : Model Xo c (RingHom.id c.F)} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z}
    {fr : EigFrame Z φ (x ≫ genι Z)} {ψ : A →+* ℂ} {y y' : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y)
    (h : SameLie y' y) : Matches fr ψ y' := by
  have e : GlobalTheory.AllWt.ptF y' = GlobalTheory.AllWt.ptF y := by
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans (h.1.trans (pullback.lift_fst _ _ _).symm)
    · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨e ▸ hm.1, fun τ i => ?_⟩
  rw [e, h.2 τ i]
  exact hm.2 τ i

theorem chr_of_some {e : Ix D → ℤ} {t : Ix D → (CAt σ)ˣ} (h : ∀ s, t (some s) = 1) :
    chr e t = toC (t none).val ^ e none := by
  classical
  have : (∏ ix, t ix ^ e ix) = t none ^ e none := by
    rw [Fintype.prod_option, Finset.prod_eq_one fun s _ => by rw [h, one_zpow], mul_one]
  exact (congrArg (fun u : (CAt σ)ˣ => toC u.val) this).trans (@Units.val_zpow_eq_zpow_val ℂ _ (t none) (e none))

theorem tendsto_punctured {f : ℂ → ℂ} (h : Tendsto (fun w => f (eTwoPi w)) imTop (𝓝 0)) :
    Tendsto f (𝓝[≠] 0) (𝓝 0) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have t₁ : Tendsto (fun u : ℂ => Complex.log u / (2 * Real.pi * Complex.I)) (𝓝[≠] 0) imTop := by
    refine tendsto_comap_iff.2 ?_
    have h₁ : Tendsto (fun u : ℂ => ‖u‖) (𝓝[≠] 0) (𝓝[>] 0) := tendsto_norm_nhdsNE_zero
    have h₂ := (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h₁)).atTop_div_const hπ
    refine h₂.congr fun u => ?_
    have e : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp only [Function.comp_apply]
    rw [e, ← div_div (Complex.log u), Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.div_ofReal_re, Complex.log_re, neg_div]
  refine (h.comp t₁).congr' (eventually_mem_nhdsWithin.mono fun u hu => ?_)
  simp only [Function.comp_apply, eTwoPi]
  rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]



theorem exists_eigFrame_tau (T : TorFlag Xo c) {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)]
    {φ : c.F →+* Γ(T.X.YY, W)} (hφ : GlobalTheory.FlagMod.tau hW ≫ flagStr T.X = spMap φ) (k : T.X.F.J)
    (hz : ⊤ ≤ GlobalTheory.FlagMod.tau hW ⁻¹ᵁ T.X.F.U k) {x' : Sp Γ(T.X.YY, W) ⟶ T.Y.X} (hx : GlobalTheory.FlagMod.tau hW ≫ T.X.π = x') :
    ∃ fr : EigFrame T.Y φ x', ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k _ hz hx τ j)).left := by
  subst hx
  let A : Type := Γ(T.X.YY, W)
  let K : Type := FractionRing A
  letI : Algebra c.F K := ((algebraMap A K).comp φ).toAlgebra
  let z : Sp K ⟶ T.X.YY := spMap (algebraMap A K) ≫ GlobalTheory.FlagMod.tau hW
  have hO : ⊤ ≤ z ⁻¹ᵁ flagOpen T.X := by
    intro s _
    let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have hs : spMap (algebraMap A K) s = η := by
      refine PrimeSpectrum.ext ?_
      let s' : PrimeSpectrum K := s
      have h0 : s'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      show Ideal.comap (algebraMap A K) s'.asIdeal = ⊥
      rw [h0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A K)
    obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen
      ⟨_, GlobalTheory.FlagMod.tau_le hW le_rfl (Set.mem_univ η)⟩
    obtain ⟨p', rfl⟩ : p ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hpW
    have hsp : η ⤳ (p' : PrimeSpectrum A) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    show GlobalTheory.FlagMod.tau hW (spMap (algebraMap A K) s) ∈ flagOpen T.X
    rw [hs]
    exact (hsp.map (GlobalTheory.FlagMod.tau hW).continuous).mem_open (flagOpen T.X).isOpen hpO
  have hr : Set.range (z ≫ T.X.π) ⊆ Set.range T.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hO (Set.mem_univ s)
  have hf := IsOpenImmersion.lift_fac T.Y.j (z ≫ T.X.π) hr
  refine GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt E H D l Xo c _ _ T.Y T.X A K φ rfl _ k hz
    (IsOpenImmersion.lift T.Y.j (z ≫ T.X.π) hr) ?_ hf.symm
  rw [← openImmersion_comp_structure_eq_generic T.Y, ← Category.assoc, hf, Category.assoc, Category.assoc]
  exact (congrArg (_ ≫ ·) hφ).trans (Spec.map_comp _ _).symm


end DifferentiableLines
end
end

section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open GlobalTheory.CxPts Filter Topology ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

theorem frequently_ne_zero {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [Smooth p] {σ : F →+* ℂ} {W : Y.Opens}
    (hW : IsAffineOpen W) [IsDomain Γ(Y, W)] {g : Γ(Y, W)} (hg : g ≠ 0) {y : GlobalTheory.CxPts p σ} (hy : y ∈ ptsIn p σ W)
    {N : Set (GlobalTheory.CxPts p σ)} (hN : N ∈ 𝓝 y) : ∃ y' ∈ N, ev p σ W g y' ≠ 0 := by
  classical
  letI : Algebra F Γ(Y, W) := (algX p W).toAlgebra
  have hs : (algX p W).Smooth :=
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.bijective).comp
      (HasRingHomProperty.appLE @Smooth p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top)
  obtain ⟨ψ, ρ, hψ, h0, hσ, hne⟩ := GlobalTheory.HolArc.exists_holPts_ne_zero F Γ(Y, W) hs (evHom hy) g hg
  have ha : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ a, ψ u (algX p W a) = σ a := fun u hu a =>
    (RingHom.congr_fun (hσ u hu) a).trans ((ev_eq hy _).symm.trans (ev_algX hy a))
  let e : ℂ → GlobalTheory.CxPts p σ := fun u => if hu : u ∈ Metric.ball (0 : ℂ) ρ then ofHom hW (ψ u) (ha u hu) else y
  have hb := Metric.ball_mem_nhds (0 : ℂ) hψ.1
  have hev : ∀ u ∈ Metric.ball (0 : ℂ) ρ, e u ∈ ptsIn p σ W ∧ ∀ f, ev p σ W f (e u) = ψ u f := fun u hu => by
    simp only [e, dif_pos hu]
    exact ⟨ofHom_mem _ _ _, ev_ofHom _ _ _⟩
  have ht : Tendsto e (𝓝 0) (𝓝 y) := by
    refine tendsto_subtype_rng.2 (GlobalTheory.Points.tendsto_of_isAffineOpen hW hy
      (eventually_of_mem hb fun u hu => (hev u hu).1) fun f => ?_)
    have h₁ := ((hψ.2 f).differentiableAt hb).continuousAt.tendsto
    rw [h0, ← ev_eq hy] at h₁
    exact h₁.congr' (eventually_of_mem hb fun u hu => ((hev u hu).2 f).symm)
  obtain ⟨u, ⟨h₁, h₂⟩, h₃⟩ := (((ht.eventually hN).and hb).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
    |>.and eventually_mem_nhdsWithin).exists
  exact ⟨e u, h₁, by rw [(hev u h₂).2]; exact hne u h₂ h₃⟩

theorem mem_open_of_ptY (T : TorFlag Xo c) (x : FrPt Xo c (CAt σ)) (y : GlobalTheory.CxPts (flagStr T.X) σ)
    (e : T.X.ptY x = zOf y) : y ∈ ptsIn _ σ (flagOpen T.X) := by
  have : ⊤ ≤ T.X.ptY x ⁻¹ᵁ flagOpen T.X := by
    rw [← T.X.pt_inc]
    exact GlobalTheory.FlagMod.le_preimage_map T.X.inc (top_le_inc T.X) le_top
  rw [e] at this
  exact this

end DifferentiableLines
end
end
