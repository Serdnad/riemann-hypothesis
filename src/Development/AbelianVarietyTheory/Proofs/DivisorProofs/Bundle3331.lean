module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3321
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import ReciprocityTheory.ReductiveGroups.Lattices.LatUnrCharA

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem unif_baseChange_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ φ : R →+* R', IsLocalHom φ → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap φ (genericPoint (Sp R')) ∈ W → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∃ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif (maximalIdeal R') D' A' G'), IsPullUnif φ hD bc U U' := by
  intro R _ _ _ hR D A G _ _ hG U R' _ _ _ hR' φ hφl W hψ hgen G' _ _ bc mbc
  obtain ⟨hL, -, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  have aR := hR.1
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  let x : Sp (FractionRing R') ⟶ Sp R := jK R' ≫ specOf φ
  have hxW : Set.range x ⊆ (W : Set (Sp R)) := by
    rintro _ ⟨z, rfl⟩
    have hz : (jK R').base z = genericPoint (Sp R') := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R' (FractionRing R')) z.asIdeal = ⊥
      haveI := z.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R' (FractionRing R'))
    show (specOf φ).base ((jK R').base z) ∈ W
    rw [hz]
    exact hgen
  obtain ⟨hamp, hkt⟩ := GlobalTheory.T.relAmple_principal_polarisation_every_fibre_of_generate R hR D A G hG U W hψ (FractionRing R') x hxW
  have hBs := IsSemiAbelian.pullback x G hG
  have hab : IsAbelianScheme ((Over.pullback x).obj G) :=
    ⟨hBs.comm, hBs.smooth, GlobalTheory.ZH.isProper_hom_of_relAmple hamp, hBs.geomConnected⟩
  have hpbG := isGrpPullback_pullback G x
  haveI := mbc
  have hbc : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hgK := (isGrpPullback_pullback G' (jK R')).comp hbc
  obtain ⟨eA, meA, heA⟩ := grpPullback_iso hgK hpbG

  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have dA : d = A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    A.smoothDim (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hdB : SmoothOfRelativeDimension A.g ((Over.pullback x).obj G).hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd
  let A' : PolAV (Sp (FractionRing R')) :=
    { A := (Over.pullback x).obj G
      isAb := hab
      g := A.g
      smoothDim := hdB
      L := U.LG.L.pull (pullback.fst G.hom x)
      isLB := pull_isLB U.LG.isLB _
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hpbG ⟨U.LG.rig, U.LG.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hpbG (GlobalTheory.WtPoint.sym_of_cp (GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns))
      ample := hamp
      ktriv := hkt }
  have wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen := by
    rw [← heA]
    exact ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩
  have he := GlobalTheory.PolBaseChange.eSec_comm hbc
  let L' : RigLB G' := ⟨U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)),
    rigPullOf (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig,
    pull_isLB U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he
      U.LG.L U.LG.rig U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G G' _ he U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _))
  have hWne : (W : Set (Sp R)).Nonempty := ⟨_, hgen⟩
  obtain ⟨D', hD, U', -, -, hP⟩ := h4.unifBaseChange R R' _ _ aR hR' φ hI D A G hG U W
    (GlobalTheory.PelCoordPull.nonempty_psiOn D.toPre W hWne hψ) hgen G' bc mbc A' rfl eA meA wA L' wL he gL rL
  exact ⟨D', A', hD, U', hP⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivSol

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def mulPull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (n : ℕ) :
    IsPullDeg φ (mulDeg D n) (mulDeg D' n) where
  e := hD.e
  e_hom := hD.e_hom
  w := hD.w
  w_gen := hD.w_gen
  he := hD.he
  w_rig := hD.w_rig
  xe := hD.xe
  c_pr := fun (x : D'.X) => by
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    show (D'.c (n • x)).left ≫ _ = specOf φ ≫ (D.c (n • hD.xe x)).left
    rw [← hx]
    exact hD.c_pr (n • x)
  W := hD.W
  psiW := ⟨fun (χ : D.X) => hD.psiW.psi (n • χ), fun (χ : D.X) => hD.psiW.psi_gen (n • χ), fun (χ : D.X) => hD.psiW.psi_eq (n • χ)⟩
  g := hD.g
  g_comm := hD.g_comm
  psi_pr := fun (x : D'.X) => by
    have h := hD.psi_pr (n • x)
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    rw [hx] at h
    exact h

theorem mulDeg_psiEven (D : DegPre R) (n : ℕ) (h : D.PsiEven) : (mulDeg D n).PsiEven :=
  fun (a : D.X) => MulDeg.corr_even_degenerationData_negPoint D h (n • a) (n • (-a)) (neg_nsmul a n)

theorem mulDeg_tauBimult (D : DegPre R) (n : ℕ) (h : D.TauBimult) : (mulDeg D n).TauBimult :=
  fun (a a' b : D.X) => MulDeg.corr_bimultiplicative_degenerationData_sums D h (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
    (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _)

theorem mulDeg_psiUnitOn (D : DegPre R) (n : ℕ) (h : ∀ y, PsiUnitOn D y Set.univ) :
    ∀ y, PsiUnitOn (mulDeg D n) y Set.univ :=
  fun (y : D.X) => h (n • y)

end GlobalTheory.DivSol

namespace GlobalTheory.DivSol

theorem exists_qkPt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  intro E _ _ _ H D' l c L R _ _ _ _hB t P iw I _ s ε e _hbal hs hdf y
  obtain ⟨g, hD, hg, -, -⟩ := hdf
  obtain ⟨DR, hR, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg polBaseChange_holds L.W R iw L.D ⊤
    (GlobalTheory.ArcPull.nonempty_psiOn_top L.D L.gen) trivial
  have hbiR : DR.TauBimult := GlobalTheory.tauBimult_of_isPullDeg globalFns_holds _ _ iw L.D DR hR L.bimult
  have hunR : ∀ y, PsiUnitOn DR y Set.univ := GlobalTheory.PullDegTop.psiUnitOn_univ hR L.gen
  have hevR : DR.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull globalFns_holds _ _ iw L.D DR hR L.even
  have hC : IsPullDeg (RingHom.id R) (mulDeg DR l.M') (GlobalTheory.PolDeg.rescale P.D.toPre g) :=
    (GlobalTheory.Mum.isPullDeg_unique_any L.W R iw (mulDeg L.D l.M') _ _ ⟨mulPull hR l.M'⟩ ⟨hD⟩).some
  obtain ⟨T, ib, β, ββ, w, hF⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData (RingHom.id R) DR hbiR hunR l.M'
  let e' : P.D.toPre.X ≃+ (Fin T.r → ℤ) := hC.xe.trans ib
  let x : (Fin T.r → ℤ) ≃+ L.D.X := e'.symm.trans e.toAddEquiv
  have hx : ∀ a, x (e' a) = e a := fun a => by simp [x]
  let ε' : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    LinearMap.mk₂ ℤ (fun u v => ε k (x u) (H.w0 • x v) + ε k (x v) (H.w0 • x u))
      (fun m₁ m₂ n => by simp only [map_add (f := _), smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x m)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
      (fun m n₁ n₂ => by simp only [map_add (f := _), smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x n)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
  have hne : ∀ i, algebraMap R (FractionRing R) (s i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hs i)
  have hgv : ∀ y, ((g y : (FractionRing R)ˣ) : FractionRing R) =
      (∏ k, algebraMap R (FractionRing R) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg y, Units.val_inv_eq_inv_val, inv_inv]
  have hcoc : ∀ a a' : P.D.toPre.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing R)ˣ) : FractionRing R) =
      ∏ i, algebraMap R (FractionRing R) (s i) ^ ((l.M' : ℤ) * ε' i (e' a) (e' a')) := by
    intro a a'
    rw [Units.val_mul, Units.val_mul, hg (a + a'), hgv a, hgv a', ← Finset.prod_inv_distrib,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i)]
    congr 1
    simp only [ε', LinearMap.mk₂_apply, hx, map_add (f := _), smul_add, LinearMap.add_apply]
    ring
  obtain ⟨β', ββ', w', hF'⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg DR l.M') (mulDeg_psiEven _ _ hevR)
    (mulDeg_tauBimult _ _ hbiR) (mulDeg_psiUnitOn _ _ hunR) ib β ββ w hF R (RingHom.id R) Function.injective_id
    P.D.toPre g hC s ε' e' (fun _ => rfl) hcoc
  obtain ⟨p, hp, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε' l.M' R P.D.toPre (RingHom.id R) s e' β' ββ' w'
    P.D.tau_bimult hF' hs (FractionRing R) (e' y)
  exact ⟨p, by rw [hp]; simp⟩

end GlobalTheory.DivSol
end
end

section

open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_prime_cast_ne_zero_of_field (k : Type) [Field k] : ∃ l : ℕ, l.Prime ∧ (l : k) ≠ 0 := by
  obtain ⟨l, hl, hlp⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  refine ⟨l, hlp, fun h => ?_⟩
  rw [CharP.cast_eq_zero_iff k (ringChar k)] at h
  rcases hlp.eq_one_or_self_of_dvd _ h with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

theorem minpoly_int_coeff_zero_ne_zero {F : Type} [Field F] [NumberField F] (x : 𝓞 F) (hx : x ≠ 0) :
    (minpoly ℤ x).coeff 0 ≠ 0 := by
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hxF : (x : F) ≠ 0 := by exact_mod_cast hx
  have h1 := minpoly.coeff_zero_ne_zero (A := ℚ) (IsIntegral.of_finite ℚ (x : F)) hxF
  have h2 : minpoly ℚ (x : F) = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ F hi
  rw [h2, coeff_map] at h1
  intro h; exact h1 (by rw [h, map_zero])

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem norm_natAbs_eq_minpoly_coeff_zero_pow {F : Type} [Field F] [NumberField F] (x : 𝓞 F) :
    ∃ r : ℕ, r * (minpoly ℤ x).natDegree = Module.finrank ℚ F ∧
      (Algebra.norm ℤ x).natAbs = ((minpoly ℤ x).coeff 0).natAbs ^ r := by
  obtain ⟨r, -, hr⟩ := ReciprocityTheory.ChartRestriction.T1.lat_cp_eq_minpoly_pow x
  have hm : (minpoly ℤ x).Monic := minpoly.monic (RingOfIntegers.isIntegral x)
  refine ⟨r, ?_, ?_⟩
  · rw [← ReciprocityTheory.ChartRestriction.T1.lat_cp_natDegree x, hr, hm.natDegree_pow]
  · have e : Algebra.norm ℤ x = (-1) ^ Module.finrank ℤ (𝓞 F) * (ReciprocityTheory.ChartRestriction.T1.lat_cp x).coeff 0 := by
      rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]; rfl
    rw [e, hr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_pow]
    simp

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem deg_eq_coeff_zero_pow_of_aeval {k : Type} [Field k] (A : AbVar k) (f : End A) (m : ℤ[X]) (hm : m.Monic)
    (hp : Prime m) (hf : aeval f m = 0) :
    ∃ e : ℕ, e * m.natDegree = 2 * A.dim ∧ (deg f.asHom : ℤ) = m.coeff 0 ^ e := by
  obtain ⟨l, hl, hl0⟩ := exists_prime_cast_ne_zero_of_field k
  have := Fact.mk hl
  obtain ⟨-, -, -, hfin, hrank⟩ := GlobalTheory.AV.AbVar.tl_free_finrank k l hl0 A
  have hchar (g : End A) :
      (charpoly g).map (algebraMap ℤ ℚ_[l]) = (vmap l g.asHom).charpoly := by
    obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k A g
    have h := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate
      k l hl0 A g ((charpoly g).map (algebraMap ℤ ℚ)) (hm.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
      (fun n => by
        rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
        simp)
    rw [← h, Polynomial.map_map]
    congr 1
  have hdet : LinearMap.det (vmap l f.asHom) = (deg f.asHom : ℚ_[l]) := by
    have hneg : (-f).asHom = -f.asHom := map_neg (End.addEquiv (X := A)) f
    have hv : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
      simp only [hneg, vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
    have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec k A (-f)).1.2.2 0
    rw [Int.cast_zero, zero_sub, neg_neg] at hev
    rw [hv, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← hchar (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrank, pow_mul,
      neg_one_sq, one_pow]
    simp
  have inj : Function.Injective (algebraMap ℤ ℚ_[l]) := RingHom.injective_int _
  let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
    (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp (tend l A)
  have hψ : ψ f = vmap l f.asHom := rfl
  have hT : aeval (vmap l f.asHom) m = 0 := by
    rw [← hψ]
    have := Polynomial.hom_eval₂ m (algebraMap ℤ (End A)) ψ f
    rw [← aeval_def, hf, map_zero, Subsingleton.elim (ψ.comp (algebraMap ℤ (End A))) (algebraMap ℤ _),
      ← aeval_def] at this
    exact this.symm
  have hdvd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank (vmap l f.asHom) (m.map (algebraMap ℤ ℚ_[l]))
    (by rw [aeval_map_algebraMap]; exact hT)
  rw [← hchar f, ← Polynomial.map_pow] at hdvd
  have hQm : (charpoly f).Monic :=
    Polynomial.monic_of_injective inj (by rw [hchar f]; exact LinearMap.charpoly_monic _)
  rw [map_dvd_map _ inj hQm] at hdvd
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp _).1 hdvd
  have hQ : charpoly f = m ^ i := eq_of_monic_of_associated hQm (hm.pow i) hi
  have hdeg : (charpoly f).natDegree = 2 * A.dim := by
    rw [← Polynomial.natDegree_map_eq_of_injective inj, hchar f, LinearMap.charpoly_natDegree, hrank]
  refine ⟨i, ?_, ?_⟩
  · rw [← hdeg, hQ, hm.natDegree_pow]
  · have e := LinearMap.det_eq_sign_charpoly_coeff (vmap l f.asHom)
    rw [hdet, ← hchar f, coeff_map, hrank, pow_mul, neg_one_sq, one_pow, one_mul, hQ, coeff_zero_eq_eval_zero,
      eval_pow, ← coeff_zero_eq_eval_zero] at e
    apply Int.cast_injective (α := ℚ_[l])
    rw [Int.cast_natCast, e, eq_intCast, Int.cast_pow]

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_and_deg_eq_norm_pow : ∀ (k : Type) [Field k] (A : AbVar k) (F : Type) [Field F] [NumberField F]
    (ι : 𝓞 F →+* End A) (d : ℕ), 2 * A.dim = d * Module.finrank ℚ F → ∀ x : 𝓞 F, x ≠ 0 →
      IsIsogeny (ι x).asHom ∧ deg (ι x).asHom = (Algebra.norm ℤ x).natAbs ^ d := by
  intro k _ A F _ _ ι d hd x hx
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hm : (minpoly ℤ x).Monic := minpoly.monic hi
  have hp : Prime (minpoly ℤ x) := (minpoly.irreducible hi).prime
  have hf : aeval (ι x) (minpoly ℤ x) = 0 := by
    have := Polynomial.hom_eval₂ (minpoly ℤ x) (algebraMap ℤ (𝓞 F)) ι x
    rw [← aeval_def, minpoly.aeval, map_zero, Subsingleton.elim (ι.comp (algebraMap ℤ (𝓞 F))) (algebraMap ℤ _),
      ← aeval_def] at this
    exact this.symm
  obtain ⟨e, he, hdeg⟩ := deg_eq_coeff_zero_pow_of_aeval A (ι x) (minpoly ℤ x) hm hp hf
  obtain ⟨r, hr, hN⟩ := norm_natAbs_eq_minpoly_coeff_zero_pow x
  have hpos : 0 < (minpoly ℤ x).natDegree := minpoly.natDegree_pos hi
  have her : e = d * r := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [he, hd, ← hr, mul_assoc]
  have hdeg' : deg (ι x).asHom = ((minpoly ℤ x).coeff 0).natAbs ^ e := by
    have := congrArg Int.natAbs hdeg
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at this
  have hval : deg (ι x).asHom = (Algebra.norm ℤ x).natAbs ^ d := by
    rw [hdeg', hN, ← pow_mul, her, mul_comm]
  refine ⟨?_, hval⟩
  by_contra h
  have h0 : deg (ι x).asHom = 0 := by
    classical
    unfold deg
    rw [ite_eq_right h]
  rw [hdeg'] at h0
  exact minpoly_int_coeff_zero_ne_zero x hx (Int.natAbs_eq_zero.1 (pow_eq_zero_iff'.1 h0).1)

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem deg_aeval_eq_prod_aroots :
    ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ),
      algebraMap ℚ Ω (deg (Polynomial.aeval f R).asHom : ℚ) =
        ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map
          (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim
    (fun F => (deg (Polynomial.aeval f F).asHom : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A
      (Polynomial.aeval f G).asHom (Polynomial.aeval f F).asHom rfl rfl).2
    rw [map_mul, End.mul_asHom, h, Nat.cast_mul, mul_comm]
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous
      K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    change (deg (∑ i, m i • End.addEquiv (Polynomial.aeval f (u i))) : ℚ) =
      (deg (End.addEquiv (Polynomial.aeval f (∑ i, m i • u i))) : ℚ)

    simp only [map_sum, map_zsmul]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = ((n : End A) - f) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    rw [e]
    exact Int.cast_natCast _

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deg_aeval_end_eq_prod_aroots : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ), algebraMap ℚ Ω (deg (A := A) (B := A) (Polynomial.aeval f R).asHom : ℚ) = ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim
    (fun F => (deg (Polynomial.aeval f F).asHom : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A
      (Polynomial.aeval f G).asHom (Polynomial.aeval f F).asHom rfl rfl).2
    change (deg (Polynomial.aeval f (F * G)).asHom : ℚ) =
      (deg (Polynomial.aeval f F).asHom : ℚ) * (deg (Polynomial.aeval f G).asHom : ℚ)
    rw [map_mul, End.mul_asHom, h, Nat.cast_mul, mul_comm]
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n
      (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    change _ = (deg (End.addEquiv (Polynomial.aeval f (∑ i, m i • u i))) : ℚ)
    simp only [map_sum, map_zsmul, End.addEquiv_apply]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = (n : End A) - f := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    change ((charpoly f).map (Int.castRingHom ℚ)).eval (n : ℚ) =
      (deg (Polynomial.aeval f (Polynomial.C n - Polynomial.X)).asHom : ℚ)
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n, e, map_natCast]
end
