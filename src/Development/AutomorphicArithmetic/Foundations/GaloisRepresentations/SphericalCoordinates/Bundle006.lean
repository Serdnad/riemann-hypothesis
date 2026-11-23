module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem exists_basis {B : Type} [CommRing B] [Algebra ℂ B] (d : ℕ) (a : Fin d → B)
    (he : (MvPolynomial.aeval a : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B).toRingHom.Etale) :
    ∃ b : Module.Basis (Fin d) B Ω[B⁄ℂ], ∀ l, b l = KaehlerDifferential.D ℂ B (a l) := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := (MvPolynomial.aeval a).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap ℂ B r = MvPolynomial.aeval a (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C])
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) B := he
  let b0 := Algebra.TensorProduct.basis B (KaehlerDifferential.mvPolynomialBasis ℂ (Fin d))
  refine ⟨b0.map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ (MvPolynomial (Fin d) ℂ) B),
    fun l => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    ← KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearEquiv.apply_symm_apply,
    show algebraMap (MvPolynomial (Fin d) ℂ) B (MvPolynomial.X l) = a l from MvPolynomial.aeval_X a l]

private theorem exists_phi {B : Type} [CommRing B] [Algebra ℂ B] (e : B →ₐ[ℂ] ℂ) (d : ℕ)
    (bs : Module.Basis (Fin d) B Ω[B⁄ℂ]) :
    ∃ φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (r : B) (ω : Ω[B⁄ℂ]), φ (r • ω) = e r • φ ω) ∧ (∀ l, φ (bs l) = Pi.single l 1) ∧
      ∀ ω : Ω[B⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → B) (ω' : Fin m → Ω[B⁄ℂ]),
        (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i := by
  let φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun ω l => e (bs.repr ω l)
      map_add' := by
        intro x y
        funext l
        simp
      map_smul' := by
        intro c x
        funext l
        rw [← algebraMap_smul B c x, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
          AlgHom.commutes]
        simp }
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro r ω
    funext l
    simp [φ]
  · intro l
    funext l'
    by_cases h : l' = l
    · subst h
      simp [φ]
    · simp [φ, Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
  · intro ω hω
    refine ⟨d, fun l => bs.repr ω l, bs, ?_, (bs.sum_repr ω).symm⟩
    intro i
    simpa [φ] using congrFun hω i

end UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tanExists_of :
    UpperTheory.Gal.W2.TanExists := by
  intro Z Y sZ s' d hsmooth c₁ c₂ h₁ h₂ hc₁ y hy
  haveI := hsmooth
  obtain ⟨U, x, hUaff, hzU, het⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := sZ) (D := d)
    ((↑y ≫ c₁ : Sp ℂ ⟶ Z) (IsLocalRing.closedPoint ℂ))
  have hyU : ⊤ ≤ (↑y : Sp ℂ ⟶ Y) ⁻¹ᵁ (c₁ ⁻¹ᵁ U ⊓ c₂ ⁻¹ᵁ U) := by
    rw [GlobalTheory.Points.le_preimage_iff]
    have h2 := hzU
    rw [hy] at h2
    exact ⟨hzU, h2⟩
  obtain ⟨V, hVaff, hyV, hVle⟩ := GlobalTheory.Points.exists_isAffineOpen_le (↑y : Sp ℂ ⟶ Y) hyU
  have hV1 : V ≤ c₁ ⁻¹ᵁ U := hVle.trans inf_le_left
  have hV2 : V ≤ c₂ ⁻¹ᵁ U := hVle.trans inf_le_right
  have hg := HasRingHomProperty.appLE @Etale c₁ hc₁ ⟨U, hUaff⟩ ⟨V, hVaff⟩ hV1
  have hres : ∀ t, (c₁.appLE U V hV1).hom t = Sec.res s' hV1 (appSec sZ s' c₁ U t) := by
    intro t
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  have heq : (MvPolynomial.aeval (fun l => Sec.res s' hV1 (appSec sZ s' c₁ U (x l))) :
      MvPolynomial (Fin d) ℂ →ₐ[ℂ] Sec s' V).toRingHom =
      (c₁.appLE U V hV1).hom.comp (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := semiHom_appSec h₁ U r 1
      simp only [Algebra.smul_def, _root_.mul_one, map_one, RingHom.id_apply] at h1
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
      have h4 : (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) (MvPolynomial.C r) =
          DVR.FlatBC.algX sZ U r := MvPolynomial.eval₂Hom_C _ _ _
      refine Eq.trans ?_ ((congrArg (c₁.appLE U V hV1).hom h4).trans (hres _)).symm
      change algebraMap ℂ (Sec s' V) r = Sec.res s' hV1 (appSec sZ s' c₁ U (algebraMap ℂ (Sec sZ U) r))
      rw [h1, AlgHom.commutes]
    · intro i
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      have h4 : (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) (MvPolynomial.X i) = x i :=
        MvPolynomial.eval₂Hom_X' _ _ _
      exact ((congrArg (c₁.appLE U V hV1).hom h4).trans (hres (x i))).symm
  have het' : (MvPolynomial.aeval (fun l => Sec.res s' hV1 (appSec sZ s' c₁ U (x l))) :
      MvPolynomial (Fin d) ℂ →ₐ[ℂ] Sec s' V).toRingHom.Etale := by
    rw [heq]
    exact RingHom.Etale.stableUnderComposition _ _ het hg
  obtain ⟨bs, hbs⟩ := UpperTheory.Gal.W2.exists_basis d _ het'
  have hyV' : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := hyV
  let e : Sec s' V →ₐ[ℂ] ℂ :=
    { toRingHom := CxPts.evHom hyV'
      commutes' := fun r => (CxPts.ev_eq hyV' _).symm.trans (CxPts.ev_algX hyV' r) }
  obtain ⟨φ, hsm, hbasis, hker⟩ := UpperTheory.Gal.W2.exists_phi e d bs
  refine ⟨fun j l => φ (KaehlerDifferential.D ℂ (Sec s' V) (Sec.res s' hV2 (appSec sZ s' c₂ U (x j)))) l,
    U, V, hV1, hV2, x, hyV', hUaff, hVaff, φ, ?_, ?_, ?_, ?_⟩
  · intro b ω
    rw [hsm]
    congr 1
    exact (CxPts.ev_eq hyV' b).symm
  · intro l
    have h3 := hbasis l
    rw [hbs l] at h3
    exact h3
  · intro j
    rfl
  · intro ω hω
    obtain ⟨m, b, ω', hb, hsum⟩ := hker ω hω
    exact ⟨m, b, ω', fun i => (CxPts.ev_eq hyV' (b i)).trans (hb i), hsum⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem map_star_inv_mul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (hdet : H.det ≠ 0) :
    (H.map star)⁻¹ * H.map star = 1 := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hb : H.map star * (H⁻¹).map star = 1 := by
    have h := congrArg (fun M => (starRingEnd ℂ).mapMatrix M) hHi
    simp only [map_mul, map_one] at h
    exact h
  have hi : (H.map star)⁻¹ = (H⁻¹).map star := Matrix.inv_eq_right_inv hb
  rw [hi]
  exact mul_eq_one_comm.mp hb

theorem UpperTheory.Gal.W2.corrChart_of :
    UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.PerLin → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart := by
  intro hAd hLin hFib O _ bar g ρ D X s A _ S k Z c₁ c₂ P₀ M₀ hP₀ hM₀ ga H hH L hL C hC hC'' z
  obtain ⟨hdet, hcomm, -⟩ := hAd O bar g ρ D P₀ M₀ hP₀ hM₀ ga H hH
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hiH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hu
  have hbi := map_star_inv_mul H hdet
  set C'' := H * C * (H.map star)⁻¹ with hC''def

  let P'' : D.La →+ (Fin g → ℂ) := (Matrix.toLin' H⁻¹).toAddMonoidHom.comp (perC P₀ C'')
  have hP''apply : ∀ x, P'' x = H⁻¹ *ᵥ perC P₀ C'' x := fun x => by
    show Matrix.toLin' H⁻¹ (perC P₀ C'' x) = _
    rw [Matrix.toLin'_apply]
  have hdetInv : (H⁻¹).det ≠ 0 := by
    intro h0
    have h1 : (H⁻¹ * H).det = 1 := by rw [hiH, Matrix.det_one]
    rw [Matrix.det_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hcommInv : ∀ a, ρ a * H⁻¹ = H⁻¹ * ρ a := fun a => by
    calc ρ a * H⁻¹ = H⁻¹ * (H * ρ a) * H⁻¹ := by
            rw [← Matrix.mul_assoc, hiH, Matrix.one_mul]
      _ = H⁻¹ * (ρ a * H) * H⁻¹ := by rw [hcomm a]
      _ = H⁻¹ * ρ a * (H * H⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H⁻¹ * ρ a := by rw [hHi, Matrix.mul_one]
  have hP'' : IsPeriod D ρ P'' :=
    hLin O bar g ρ D (perC P₀ C'') P'' H⁻¹ hC'' hdetInv hcommInv hP''apply
  have hga : ∀ x, P'' (ga x) = perC P₀ C x := fun x => by
    rw [hP''apply, perC_apply, perC_apply, hH.2 x, GlobalTheory.PerCoordU.star_mulVec_map,
      Matrix.mulVec_mulVec, hC''def]
    have e : H * C * (H.map star)⁻¹ * H.map star = H * C := by
      rw [Matrix.mul_assoc, hbi, Matrix.mul_one]
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hcorr := hL (perC P₀ C) P'' hC hP'' hga z
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear (Matrix.toLin' H) (Matrix.toLin' H⁻¹)
    (by rw [← Matrix.toLin'_mul, hHi, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hiH, Matrix.toLin'_one])
  have happ : ∀ v, h v = H *ᵥ v := fun v => by
    show Matrix.toLin' H v = _
    rw [Matrix.toLin'_apply]
  have hfib := (hFib O bar g ρ D X s A S k P'' hP'').2.2.2.2 (perC P₀ C'') h hC''
    (fun x => by rw [happ, hP''apply, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]) (L z)
  have hz : fibMap H L z = fun j => h (L z j) := by
    funext j
    rw [happ]
    simp [fibMap, Matrix.toLin'_apply]
  rw [hz, hfib]
  exact hcorr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_map_ext {X : Scheme.{0}} {A : Over X} {k : ℕ} {T : Scheme.{0}}
    (a b : T ⟶ (GlobalTheory.KS.pow A k).left) (h0 : a ≫ (GlobalTheory.KS.pow A k).hom = b ≫ (GlobalTheory.KS.pow A k).hom)
    (h : ∀ j, a ≫ (GlobalTheory.KS.pr A j).left = b ≫ (GlobalTheory.KS.pr A j).left) : a = b := by
  let Y : Over X := Over.mk (a ≫ (GlobalTheory.KS.pow A k).hom)
  let fa : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk a rfl
  let fb : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk b h0.symm
  have hab : fa = fb := by
    unfold GlobalTheory.KS.pow at fa fb ⊢
    apply Limits.Pi.hom_ext
    intro j
    ext
    simp only [Over.comp_left, Over.homMk_left, fa, fb]
    exact h j
  exact congrArg (fun f => f.left) hab

section
variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D : PLat O bar}
  {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {A : Over X} [GrpObj A] (S : Sheet s A D ρ) (k : ℕ)

private theorem pt_hom (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) :
    S.pt k P z ≫ (GlobalTheory.KS.pow A k).hom = S.u P :=
  Over.w (Pi.lift (fun j => S.ex P (z j)) : Over.mk (S.u P) ⟶ GlobalTheory.KS.pow A k)

private theorem pt_pr (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) (j : Fin k) :
    S.pt k P z ≫ (GlobalTheory.KS.pr A j).left = (S.ex P (z j)).left := by
  unfold Sheet.pt GlobalTheory.KS.pr
  rw [← Over.comp_left]
  exact congrArg Over.Hom.left (Limits.Pi.lift_comp_π _ j)

private theorem ex_sub (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ρ P) (a b : Fin g → ℂ) :
    S.ex P a = S.ex P (a - b) * S.ex P b := by
  have h := S.exp P hP
  unfold IsExp at h
  have e := h.1 (a - b) b
  rwa [sub_add_cancel] at e

end

theorem UpperTheory.Gal.W2.ptFibre_of :
    UpperTheory.Gal.W2.PtFibre := by
  intro O _ bar g ρ D X s A _ S k P hP
  have hE := S.exp P hP
  unfold IsExp at hE
  have hu : ∀ (P' : D.La →+ (Fin g → ℂ)) (w : Fin g → ℂ), (S.ex P' w).left ≫ A.hom = S.u P' :=
    fun P' w => Over.w (S.ex P' w)
  refine ⟨fun z => pt_hom S k P z, fun z j => pt_pr S k P z j, ?_, ?_, ?_⟩
  · intro y hy
    have hc : ∀ j : Fin k, ∃ w, S.ex P w =
        Over.homMk (U := Over.mk (S.u P)) (V := A) (y ≫ (GlobalTheory.KS.pr A j).left) (by
          show _ = S.u P
          rw [Category.assoc, Over.w]
          exact hy) := fun j => hE.2.1 _
    choose z hz using hc
    refine ⟨z, pow_map_ext _ _ ?_ ?_⟩
    · rw [hy, pt_hom]
    · intro j
      rw [pt_pr, hz j]
      rfl
  · intro z z'
    constructor
    · intro heq j
      have e1 : (S.ex P (z j)).left = (S.ex P (z' j)).left := by
        rw [← pt_pr S k P z j, ← pt_pr S k P z' j, heq]
      have e2 : S.ex P (z j) = S.ex P (z' j) := Over.OverMorphism.ext e1
      have e3 : S.ex P (z j - z' j) = 1 := by
        have e4 := ex_sub S P hP (z j) (z' j)
        rw [e2] at e4
        exact mul_eq_right.mp e4.symm
      exact (S.ker P hP _).mp e3
    · intro hr
      apply pow_map_ext
      · rw [pt_hom, pt_hom]
      · intro j
        rw [pt_pr, pt_pr, ex_sub S P hP (z j) (z' j), (S.ker P hP _).mpr (hr j), _root_.one_mul]
  · intro P' h hP' hx z
    have hu' : S.u P' = S.u P := by
      calc S.u P' = (S.ex P' (h 0)).left ≫ A.hom := (hu P' (h 0)).symm
        _ = (S.ex P 0).left ≫ A.hom := by rw [S.lin P P' h hP hP' hx 0]
        _ = S.u P := hu P 0
    apply pow_map_ext
    · rw [pt_hom, pt_hom, hu']
    · intro j
      rw [pt_pr, pt_pr]
      exact S.lin P P' h hP hP' hx (z j)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem det_lattice_restrict_eq_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Lz : Submodule ℤ E) [DiscreteTopology Lz] [IsZLattice ℝ Lz]
    (f : E →ₗ[ℝ] E) (fL : Lz →ₗ[ℤ] Lz) (hfL : ∀ x, (fL x : E) = f x) :
    ((LinearMap.det fL : ℤ) : ℝ) = LinearMap.det f := by
  haveI := ZLattice.module_free ℝ Lz
  haveI := ZLattice.module_finite ℝ Lz
  let b := Module.Free.chooseBasis ℤ Lz
  let bR := Module.Basis.ofZLatticeBasis ℝ Lz b
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bR, ← eq_intCast (Int.castRingHom ℝ),
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.ofZLatticeBasis_apply, ← hfL, Module.Basis.ofZLatticeBasis_repr_apply]
  rfl

private theorem exists_lattice_reps {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : AddSubgroup E) (hd : DiscreteTopology L)
    (hs : Submodule.span ℝ (L : Set E) = ⊤) (f : E →ₗ[ℝ] E) (hf : ∀ z ∈ L, f z ∈ L)
    (hdet : LinearMap.det f ≠ 0) :
    ∃ Fz : Finset E, (∀ z ∈ Fz, f z ∈ L) ∧ (∀ z, f z ∈ L → ∃! z', z' ∈ Fz ∧ z - z' ∈ L) ∧
      (Fz.card : ℝ) = |LinearMap.det f| := by
  classical
  let Lz : Submodule ℤ E := AddSubgroup.toIntSubmodule L
  haveI : DiscreteTopology Lz := hd
  haveI : IsZLattice ℝ Lz := ⟨hs⟩
  haveI := ZLattice.module_free ℝ Lz
  haveI := ZLattice.module_finite ℝ Lz
  let fL : Lz →ₗ[ℤ] Lz :=
    { toFun := fun x => ⟨f x, hf x x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp }
  have hfL : ∀ x, (fL x : E) = f x := fun x => rfl
  have hdetZ := det_lattice_restrict_eq_det Lz f fL hfL
  have hdetL : LinearMap.det fL ≠ 0 := by
    intro h; apply hdet; rw [← hdetZ, h]; simp
  let fe := LinearMap.equivOfDetNeZero f hdet
  have hfe : ∀ z, fe z = f z := fun z => rfl
  have finj : Function.Injective f := by
    intro x y h; apply fe.injective; rw [hfe, hfe, h]
  have hinj : Function.Injective fL := fun x y h => Subtype.ext (finj (congrArg Subtype.val h))
  let N := LinearMap.range fL
  let e := LinearEquiv.ofInjective fL hinj
  have hcard := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ (e : Lz →+ N).toIntLinearMap = fL := by ext x; rfl
  rw [hcomp] at hcard
  haveI : Finite (Lz ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [← hcard]; exact Int.natAbs_ne_zero.mpr hdetL)
  letI := Fintype.ofFinite (Lz ⧸ N)
  let s : (Lz ⧸ N) → E := fun q => fe.symm ((Quotient.out q : Lz) : E)
  have hs_f : ∀ q, f (s q) = ((Quotient.out q : Lz) : E) := fun q => by
    rw [← hfe]; exact fe.apply_symm_apply _
  have hsinj : Function.Injective s := by
    intro q q' h
    have h1 : (Quotient.out q : Lz) = Quotient.out q' := Subtype.ext (by rw [← hs_f, ← hs_f, h])
    rw [← Submodule.Quotient.mk_out q, ← Submodule.Quotient.mk_out q', h1]
  have key : ∀ z (hz : f z ∈ L) (q' : Lz ⧸ N),
      z - s q' ∈ L ↔ q' = Submodule.Quotient.mk (⟨f z, hz⟩ : Lz) := by
    intro z hz q'
    constructor
    · intro h
      have hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N :=
        ⟨⟨z - s q', h⟩, by ext; simp [fL, hs_f]⟩
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out] at hm
      exact hm.symm
    · intro h
      have hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N := by
        rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out, h]
      obtain ⟨l, hl⟩ := hm
      have : f (l : E) = f (z - s q') := by
        rw [← hfL, hl, map_sub, hs_f]; rfl
      rw [← finj this]; exact l.2
  refine ⟨Finset.univ.image s, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hs_f]; exact (Quotient.out q).2
  · intro z hz
    refine ⟨s (Submodule.Quotient.mk (⟨f z, hz⟩ : Lz)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (key z hz _).mpr rfl⟩, ?_⟩
    rintro z' ⟨hz', hzz'⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz'
    rw [(key z hz q).mp hzz']
  · rw [Finset.card_image_of_injective _ hsinj, Finset.card_univ, ← Nat.card_eq_fintype_card, ← hcard,
      ← hdetZ, Nat.cast_natAbs, Int.cast_abs]

theorem UpperTheory.Gal.W2.torusCount_of :
    UpperTheory.Gal.W2.DetReal → UpperTheory.Gal.W2.TorusCount := by
  intro hDR W _ _ _ Λ hd hs Θ hΘ hdet
  let f : W →ₗ[ℝ] W := (1 - Θ).restrictScalars ℝ
  have hR : ((LinearMap.det f : ℝ) : ℂ) = _ := hDR W (1 - Θ)
  have hdf : LinearMap.det f = Complex.normSq (LinearMap.det (1 - Θ)) := by
    apply Complex.ofReal_injective
    rw [hR, Complex.mul_conj]
  have hfz : ∀ z, f z ∈ Λ ↔ Θ z - z ∈ Λ := by
    intro z
    show (1 - Θ) z ∈ Λ ↔ _
    rw [LinearMap.sub_apply, Module.End.one_apply, ← neg_sub, neg_mem_iff]
  have hfL : ∀ z ∈ Λ, f z ∈ Λ := fun z hz => (hfz z).mpr (sub_mem (hΘ z hz) hz)
  have hpos : 0 < LinearMap.det f := by rw [hdf]; exact Complex.normSq_pos.mpr hdet
  obtain ⟨Fz, h1, h2, h3⟩ := exists_lattice_reps Λ hd hs f hfL hpos.ne'
  refine ⟨Fz, fun z hz => (hfz z).mp (h1 z hz), fun z hz => h2 z ((hfz z).mpr hz), ?_⟩
  rw [Complex.mul_conj, ← hdf, ← abs_of_pos hpos, ← h3]
  norm_cast
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem expImm0_of : ExpImm0 := by
  intro X A _ g y e he w hw
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  have hv0 : IsDerivAt0 (fun z => Over.Hom.left (e z)) 0 (Over.Hom.left v) := by
    refine ⟨hv.1, fun U h f => (hv.2 U h f).trans ?_⟩
    have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ Over.Hom.left v = Over.Hom.left (e 0) := hv.1
    have h' : ⊤ ≤ (Over.Hom.left (e 0)) ⁻¹ᵁ U := by
      rw [← hb]
      exact fun x _ => h trivial
    rw [hw U f h', map_zero]
  exact (he.2.2.2.2 v hv.1).unique hv hv0

end UpperTheory.Gal.W2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatPre_of :
    UpperTheory.Gal.W2.FlatPre := by
  intro V _ _ V' _ _ Y B s hs φ φ' v₀ w hφ hB
  have key : ∀ (U : Y.Opens) (f : Γ(Y, U)), ⊤ ≤ s (φ v₀) ⁻¹ᵁ U →
      fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ w =
        fderiv ℂ (fun b => valAt' (s b) U f) (φ v₀) (φ' w) := by
    intro U f hU
    obtain ⟨hopen, hdiff⟩ := hs U f
    have hmem : φ v₀ ∈ {b ∈ B | ⊤ ≤ s b ⁻¹ᵁ U} := ⟨hB, hU⟩
    have hd : DifferentiableAt ℂ (fun b => valAt' (s b) U f) (φ v₀) :=
      (hdiff _ hmem).differentiableAt (hopen.mem_nhds hmem)
    have hc := hd.hasFDerivAt.comp v₀ hφ
    have he : fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ = _ := hc.fderiv
    rw [he]
    rfl
  constructor
  · intro h U f hU
    rw [← key U f hU]
    exact h U f hU
  · intro h U f hU
    rw [key U f hU]
    exact h U f hU
end
