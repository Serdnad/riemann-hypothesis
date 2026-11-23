module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernLine

theorem eq_homogeneousComponent {κ R : Type} [AddCommGroup R] (f : MvPolynomial κ ℝ →+ R) (D : ℕ)
    (hf : ∀ d, d ≠ D → ∀ Q : MvPolynomial κ ℝ, Q.IsHomogeneous d → f Q = 0) (P : MvPolynomial κ ℝ) :
    f P = f (homogeneousComponent D P) := by
  conv_lhs => rw [← sum_homogeneousComponent P]

  rw [map_sum, Finset.sum_eq_single D]
  · intro b _ hb
    exact hf b hb _ (homogeneousComponent_isHomogeneous b P)
  · intro hD
    rw [Finset.mem_range, not_lt] at hD
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem interPoly_eq_zero {F : Type} [Field F] (Y : Var F) {κ : Type} (Δ : κ → Y.Dv) (d : ℕ) (hd : d ≠ Y.dim)
    (Q : MvPolynomial κ ℝ) (hQ : Q.IsHomogeneous d) : Y.interPoly Δ Q = 0 := by
  classical

  rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' : m.degree = d := by
    have := hQ (mem_support_iff.mp hm)
    first
    | (rw [Finsupp.degree_eq_weight_one]; exact this)
    | exact this
  rw [show monomial m (AddMonoidAlgebra.coeff Q m) = AddMonoidAlgebra.coeff Q m • basisMonomials κ ℝ m by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, Var.interPoly, Module.Basis.constr_basis, dite_eq_right, smul_zero]
  rintro ⟨s, hs⟩
  apply hd

  rw [← hm', ← hs, map_sum]
  simp

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hC F _ σ X κ _ Δ L r ψ hψ P
  have hR : X.interPoly Δ P = X.interPoly Δ (homogeneousComponent X.dim P) :=
    eq_homogeneousComponent (X.interPoly Δ).toAddMonoidHom X.dim (fun d hd Q hQ => interPoly_eq_zero X Δ d hd Q hQ) P
  have hL : ∀ x, dens (evalF (atlas X σ) (fun a => c1W (ψ a)) P x) =
      dens (evalF (atlas X σ) (fun a => c1W (ψ a)) (homogeneousComponent X.dim P) x) := by
    intro x
    let f : MvPolynomial κ ℝ →+ ℂ :=
      { toFun := fun Q => dens (evalF (atlas X σ) (fun a => c1W (ψ a)) Q x)
        map_zero' := by simp [evalF, LineForm.fld, dens]
        map_add' := fun Q Q' => by
          simp only [evalF, LineForm.fld, map_add (f := _), Subalgebra.coe_add]
          exact LineForm.TopInt.dens_add _ _ }
    refine eq_homogeneousComponent f X.dim (fun d hd Q hQ => ?_) P
    exact GlobalTheory.T.topDensity_hermitianForms_eq_zero_offDegree X.dim κ _ d Q hQ hd
  rw [hR, ← GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber hC F σ X κ Δ L r ψ hψ _ (homogeneousComponent_isHomogeneous _ P)]
  simp only [HolAtlas.integral, LineForm.TopInt.part_congr _ hL]

end GlobalTheory.ChernLine
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_thMap_of_affine_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    IsReduced X → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U)) →
    ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hmu hn hred hP hA
  have hloc : ∀ x : X, ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧
      ThMap G L ρ m (W.ι ≫ q) h := by
    intro x
    obtain ⟨U, hxU, h1, h2, h3, h4⟩ := hA x
    exact GlobalTheory.T.exists_nhd_thetaMap_on_normal_charZero_affine S G L ρ hL hρ g m n o X s q hmo hm3 hmu hn hP U h1 h2 h3 h4 x hxU
  choose W h hxW hs hT using hloc
  have hag : ∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ h i = y' ≫ h j := by
    intro i j K _ _ y y' e
    have hPK := hP K (y ≫ (W i).ι)
    obtain ⟨⟨θ, hθ⟩, -⟩ := gen_of_polFib S G L hL g K _ hPK
    have hmK : (m : K) ≠ 0 := by
      have := hmu.map (Spec.preimage (y ≫ (W i).ι ≫ s)).hom
      rw [map_natCast] at this
      exact this.ne_zero
    obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) K _ θ hmo hmK hn hPK
    have hH : HasTh G L ρ m ((y ≫ (W i).ι) ≫ q) c := ⟨θ, pt, hθ, hc⟩
    have h1 := hT i K y c (by rw [Category.assoc] at hH; exact hH)
    have h2 := hT j K y' c (by rw [e, Category.assoc] at hH; exact hH)
    refine CrdUniq.eq_of_pCrd ?_ h1 h2
    rw [Category.assoc, Category.assoc, hs, hs, ← Category.assoc, e, Category.assoc]
  have hcov : (⨆ x, W x) = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨f, hf, hfi⟩ := GlobalTheory.ThetaGlue.glue_geom o n X s X W h hcov hs hag
  refine ⟨f, hf, fun K _ x c hH => ?_⟩
  let z : X := x.base (IsLocalRing.closedPoint K)
  have hr : Set.range x.base ⊆ Set.range (W z).ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim p (IsLocalRing.closedPoint K)]
    exact hxW z
  let x' : Sp K ⟶ (W z).toScheme := IsOpenImmersion.lift (W z).ι x hr
  have hx : x' ≫ (W z).ι = x := IsOpenImmersion.lift_fac _ _ _
  have h1 := hT z K x' c (by rw [← Category.assoc, hx]; exact hH)
  rw [← hx, Category.assoc, hfi]
  exact h1

theorem exists_thAt : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ), P.g = 8 * g → GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) → rig.IsGen → Odd m → 3 ≤ m → IsUnit (m : cycAway n) → ∃ (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f := by
  intro g n hg hn hno F W hW P rig m hPg hSh hrig hmo hm3 hmu
  obtain ⟨hI, hN, hLN⟩ := GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn hno F
  letI := P.isAb.comm
  have hpos : 0 < m ^ (4 * (8 * g)) := pow_pos (by omega) _
  have hA : ∀ x : F.X, ∃ U : F.X.affineOpens, x ∈ (U : F.X.Opens) ∧ IsDomain Γ(F.X, U) ∧ IsNoetherianRing Γ(F.X, U) ∧
      IsIntegrallyClosed Γ(F.X, U) ∧ CharZero Γ(F.X, U) := fun x => by
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp F.X.isBasis_affineOpens)
      (show x ∈ (⊤ : F.X.Opens) from trivial)
    have hne : (U : F.X.Opens) ≠ ⊥ := fun h => by simp [h] at hxU
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.affineOpen_ring_isDomain_noetherian_integrallyClosed F.X hI hN hLN ⟨U, hU⟩ hne
    exact ⟨⟨U, hU⟩, hxU, h1, h2, h3, GlobalTheory.SiegelTor.sFam_charZero_affineOpen g n F ⟨U, hU⟩ inferInstance⟩
  obtain ⟨f, hf, hT⟩ := exists_thMap_of_affine_cover F.X P.A P.L rig P.isLB hrig P.g m (m ^ (4 * (8 * g)) - 1) (cycAway n) F.X F.s (𝟙 F.X)
    hmo hm3 hmu (by rw [hPg]; omega) inferInstance (fun R _ x => by simpa using GlobalTheory.UMin.FibExist.polFib_of_point F.X P R x) hA
  exact ⟨_, f, hPg, hSh, hrig, hmo, hm3, hmu, by omega, hf, hT, hW⟩

end GlobalTheory.SiegTh

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem steinFibre_subset_range : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (H' : E.H.toScheme.Opens) (X'' : Scheme.{0}) (ν : X'' ⟶ pullback (PSpace.str R E.N) M.π) (i : H'.toScheme ⟶ X'') (P'' : Scheme.{0}) (a'' : X'' ⟶ P'') (b'' : P'' ⟶ PSpace R E.N), IsFinite ν → IsOpenImmersion i → i ≫ ν = H'.ι ≫ pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over → a'' ≫ b'' = ν ≫ pullback.fst (PSpace.str R E.N) M.π → IsFinite b'' → IsProper a'' → (∀ y : P'', _root_.IsPreconnected {x : X'' | a'' x = y}) → (∀ h : E.H.toScheme, M.π (G'.hom (E.H.ι h)) = closedPoint R → h ∈ H') → ∀ z : H'.toScheme, M.π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R → ∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i := by
  intro R _ _ _ hR M G' _ _ hG E H' X'' ν i P'' a'' b'' hν hi hcomm hab hb ha hconn hH0 z hz w hw
  haveI := hν; haveI := hb; haveI := ha; haveI := hi
  have hsep : IsSeparated (a'' ≫ b'') := inferInstance
  have hR' : IsNoetherianRing R := hR.1
  have hog : i ≫ a'' ≫ b'' = H'.ι ≫ E.f := by
    rw [hab, ← Category.assoc, hcomm, Category.assoc]
    exact congrArg (H'.ι ≫ ·) (pullback.lift_fst _ _ _)
  have hy : PSpace.str R E.N (b'' (a'' (i z))) = closedPoint R := by
    have h1 : i ≫ a'' ≫ b'' ≫ PSpace.str R E.N = H'.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by
      rw [reassoc_of% hog, E.f_over]
    have h2 := congrArg (fun f => f.base z) h1
    simp only [Scheme.Hom.comp_base, ContinuousMap.comp_apply] at h2
    exact h2.trans hz
  obtain ⟨C, hC, hCeq⟩ := GlobalTheory.T.embeddedPart_points_over_closedProjPoint_closed R M.S M.π M.proper G' hG.smooth E H' X'' i (a'' ≫ b'') hsep hog hH0
    (b'' (a'' (i z))) hy
  have hfib : ∀ p : X'', a'' p = a'' (i z) → p ∈ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} := by
    intro p hp
    show b'' (a'' p) = b'' (a'' (i z))
    rw [hp]
  have key : ∀ p : X'', a'' p = a'' (i z) → p ∈ C → p ∈ Set.range i := fun p hp hpC =>
    (show p ∈ Set.range i ∩ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} from hCeq ▸ ⟨hpC, hfib p hp⟩).1
  by_contra hwi
  have hU : IsOpen (Set.range i) := i.isOpenEmbedding.isOpen_range
  obtain ⟨p, hpF, hpU, hpC⟩ := hconn (a'' (i z)) (Set.range i) Cᶜ hU hC.isOpen_compl
    (fun p hp => by
      by_cases h : p ∈ C
      · exact Or.inl (key p hp h)
      · exact Or.inr h)
    ⟨i z, rfl, z, rfl⟩ ⟨w, hw, fun h => hwi (key w hw h)⟩
  exact hpC (show p ∈ C ∩ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} from hCeq.symm ▸ ⟨hpU, hfib p hpF⟩).1

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (h : T.V →+* R) (hK : FractionRing T.V →+* FractionRing R), IsLocalHom h → (∀ a, hK (algebraMap T.V _ a) = algebraMap R _ (h a)) → ∀ c pr, SharpBy F W A' (spMap hK ≫ T.y) c pr → ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧ Associated r (h T.ϖ ^ (qW W T.β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
  first | exact @GlobalTheory.Poinc.TraitPow.exists_equiv | exact GlobalTheory.Poinc.TraitPow.exists_equiv | (intros; apply GlobalTheory.Poinc.TraitPow.exists_equiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (f : R), (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∀ tO : SAB H (Sp (Localization.Away f)), SABMap tO t (spMap (algebraMap R (Localization.Away f))) → IsProper tO.G.hom ∧ Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
  first | exact @GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn | exact GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn | (intros; apply GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PolFibre

theorem generic_fibre {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) :
    IsProper (pullback.snd G.hom (jK R)) ∧
      RelAmple ((Over.pullback (jK R)).obj G) (U.LG.L.pull (pullback.fst G.hom (jK R))) ∧
      KTriv ((Over.pullback (jK R)).obj G) (U.LG.L.pull (pullback.fst G.hom (jK R))) := by
  have := U.gen_hom
  have hiso := isGrpPullback_of_iso U.gen
  have hLG : U.LG.L.IsLB := U.LG.isLB
  obtain ⟨w, hw⟩ : LBIso (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left) := by
    obtain ⟨w, hw⟩ := U.ext
    exact LBIso.symm ⟨w, hw⟩
  have hpw := (isGen_iff w).1 hw
  have : IsIso U.gen.hom.left := ((Over.forget _).mapIso U.gen).isIso_hom
  have := A.isAb.proper
  refine ⟨?_, relAmple_pull hiso.1 A.isLB (pull_isLB hLG _) hpw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample,
    kTriv_pull hiso A.isLB (pull_isLB hLG _) hpw A.ktriv⟩
  have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  rw [← e]
  infer_instance

theorem eq_generic {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] (x : Sp K ⟶ Sp R)
    (h0 : (x (closedPoint K) : PrimeSpectrum R).asIdeal = ⊥) : x (closedPoint K) = jK R (closedPoint (FractionRing R)) := by
  refine PrimeSpectrum.ext ?_
  rw [h0]
  show ⊥ = Ideal.comap (algebraMap R (FractionRing R)) (maximalIdeal (FractionRing R))
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]

theorem relAmple_kTriv_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R), Set.range x ⊆ (W : Set (Sp R)) → RelAmple ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) := by
  intro R _ _ _ hR D A G _ _ hG U W hW K _ x hx
  obtain ⟨-, hp⟩ := GlobalTheory.T.abelian_proper_uniformised_where_trivialisations_generate R hR D A G hG U W hW
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hy : x (closedPoint K) ∈ W := hx ⟨_, rfl⟩
  by_cases h0 : (x (closedPoint K) : PrimeSpectrum R).asIdeal = ⊥
  · obtain ⟨h1, h2, h3⟩ := generic_fibre U
    exact GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point (Sp R) G hG.quasiCompact hG.separated U.smooth U.LG.L hLG (FractionRing R) (jK R) h1 h2 h3 K x
      (eq_generic x h0)
  · obtain ⟨K₁, _, z, hz, h1, h2, h3⟩ := GlobalTheory.T.exists_fieldPoint_polarised_fibre_uniformised R hR D A G hG U W hp (x (closedPoint K)) hy h0
    exact GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point (Sp R) G hG.quasiCompact hG.separated U.smooth U.LG.L hLG K₁ z h1 h2 h3 K x hz.symm

end GlobalTheory.Mum.PolFibre
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem eq_of_secRatioEq_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k), w ∈ N ∧ ∀ (W : Scheme.{0}) (a b : W ⟶ (thickObj R (maximalIdeal R) e G).left), a ≫ (thickObj R (maximalIdeal R) e G).hom = b ≫ (thickObj R (maximalIdeal R) e G).hom → (∀ x, a x ∈ N) → (∀ x, b x ∈ N) → (∀ l, SecRatioEq U.LG.L (a ≫ (fstG (maximalIdeal R) e G).left) (b ≫ (fstG (maximalIdeal R) e G).left) (σ l) s₀ (σ l) s₀) → a = b := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, H⟩ := GlobalTheory.T.exists_section_ratios_generate_mod_maximal R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk s₀ i w hw hu => ?_⟩
  obtain ⟨N, m, σ, r, hwN, hNaff, hNi, hgerm, hgen⟩ := H e k hk s₀ i w hw hu
  have hw' : (fstG (maximalIdeal R) e G).left ≫ G.hom = (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e :=
    (fstG (maximalIdeal R) e G).w
  have hz : ∀ x ∈ maximalIdeal R ^ (e + 1), (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) x = 0 := by
    intro x hx
    have h0 : (thick R (maximalIdeal R) e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = 0 := by
      have := congrArg (fun φ => φ.hom x)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      rw [← this, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, hw', Scheme.Hom.comp_appTop, CommRingCat.hom_comp, h0, map_zero]
  have hgen' := GlobalTheory.T.localized_presentation_eval_quotient_fraction R _ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) (e + 1) hz m r hgen
  refine ⟨N, m, σ, hwN, fun W a b hab ha hb hrat => ?_⟩
  have ha' : ⊤ ≤ a ⁻¹ᵁ N := fun x _ => ha x
  have hb' : ⊤ ≤ b ⁻¹ᵁ N := fun x _ => hb x
  have hst : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (f : Γ((thickObj R (maximalIdeal R) e G).left, N)), c x ∈ N →
      (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) = gs c x N f := by
    intro c x f h
    have e1 : gs (c ≫ 𝟙 _) x N f = (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) := by
      rw [gs_eq (𝟙 _) (c x) _ h, ← gs_pull c (𝟙 _) x _ h, gs_eq c x _ (show c x ∈ (𝟙 (thickObj R (maximalIdeal R) e G).left : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) ⁻¹ᵁ N from h)]
      exact (Scheme.Hom.germ_stalkMap_apply c _ x h _).symm
    rw [← e1, Category.comp_id]
  have hsg : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (s : H0 U.LG.L k), c x ∈ N →
      secGerm (c ≫ (fstG (maximalIdeal R) e G).left) x s i = (c.stalkMap x).hom (secGerm (fstG (maximalIdeal R) e G).left (c x) s i) :=
    fun c x s h => secGerm_comp c _ x s (hNi h)
  refine GlobalTheory.T.eq_of_agree_on_affineOpen_generators R _ W ((fstG (maximalIdeal R) e G).left ≫ G.hom) N hNaff m r hgen' a b ?_ ha' hb' ?_
  · rw [hw', ← Category.assoc, hab, Category.assoc]
  · intro l
    apply fn_ext
    intro x _
    rw [gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_pull (𝟙 W) a x N (ha x), gs_pull (𝟙 W) b x N (hb x), Category.id_comp, Category.id_comp]
    have key := secRatioEq_iff_germ.1 (hrat l) x i i (hNi (ha x)) (hNi (hb x))
    rw [hsg a x _ (ha x), hsg a x _ (ha x), hsg b x _ (hb x), hsg b x _ (hb x),
      (hgerm _ (ha x)).2 l, (hgerm _ (hb x)).2 l, map_mul, map_mul, hst a x _ (ha x), hst b x _ (hb x)] at key
    have hA := ((hgerm _ (ha x)).1).map (a.stalkMap x).hom
    have hB := ((hgerm _ (hb x)).1).map (b.stalkMap x).hom
    refine (hA.mul hB).mul_left_inj.1 ?_
    linear_combination key

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

theorem GlobalTheory.Mum.TensTor.zpow_sum_tens {M κ : Type} [CommGroup M] (a : M) (s : Finset κ) (f : κ → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem GlobalTheory.Mum.TensTor.tate_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∀ (Dm : Datum H) (g : ℕ) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) → (∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) → (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) → (∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F)) → ∃ I : TateIsoQ Dm D'.toPre o F, I.ζ = ζ := by
  intro R _ _ _ hB E _ _ _ H D D' r W _ hdet T ρ hρ _ _ o hact _ Dm g e _ he hEF F _ _ _ ζ hprim hpow ev hadd hker
    honto htow hweil

  obtain ⟨N, ⟨ν⟩⟩ := GlobalTheory.T.exists_degenerationValues_algClosed_field R hB D F
  obtain ⟨N', ⟨ν'⟩⟩ := GlobalTheory.T.exists_degenerationValues_algClosed_field R hB D' F
  choose P hP using fun (n : ℕ) (a : Dm.La) =>
    GlobalTheory.T.exists_tensor_torsion_point_of_component_tuple R hB D D' W T F N N' ν ν' n (fun j => ev n (e a j))
  refine ⟨⟨ζ, hprim, hpow, P, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  ·
    intro n hn a b
    have hs := hP n (a + b)
    simp only [map_add (f := _), Pi.add_apply] at hs
    exact GlobalTheory.T.tensor_torsion_add_componentwise R hB D D' W T F N N' ν ν' n (P n a) (P n b) (P n (a + b)) _ _ _ (hP n a) (hP n b) hs
      (fun i => hadd n hn (e a i) (e b i))
  ·
    intro n hn x a
    have hs := hP n (x • a)
    simp only [he] at hs
    exact GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix R hB D D' W T F N N' ν ν' E H ρ hρ o hact g ev hadd hker n hn x (fun j => e a j)
      (P n a) (P n (x • a)) (hP n a) hs
  ·
    intro n hn a b
    rw [GlobalTheory.T.tensor_torsion_point_equiv_iff_components_equiv R hB D D' W T F N N' ν ν' hdet n (P n a) (P n b) _ _ (hP n a) (hP n b)]
    simp only [hker n hn]
    constructor
    · intro h
      choose c hc using h
      refine ⟨e.symm c, e.injective ?_⟩
      rw [map_add (f := _), map_nsmul, e.apply_symm_apply]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, hc i]
    · rintro ⟨c, rfl⟩ i
      exact ⟨e c i, by simp only [map_add (f := _), map_nsmul, Pi.add_apply, Pi.smul_apply]⟩
  ·
    intro n hn p
    obtain ⟨ps, hps⟩ := GlobalTheory.T.exists_component_tuple_tensor_torsion_unimodular R hB D D' W T F N N' ν ν' hdet n p
    choose a ha using fun i => honto n hn (ps i)
    refine ⟨e.symm a, ?_⟩
    rw [GlobalTheory.T.tensor_torsion_point_equiv_iff_components_equiv R hB D D' W T F N N' ν ν' hdet n (P n (e.symm a)) p _ ps (hP n (e.symm a)) hps]
    intro i
    simpa only [e.apply_symm_apply] using ha i
  ·
    intro n m hn hm a
    exact GlobalTheory.T.tensor_torsion_tower_nsmul_componentwise R hB D D' W T F N N' ν ν' n m hn hm (P (n * m) a) _ (P n a) _ (hP (n * m) a) (hP n a)
      (fun i => htow n m hn hm (e a i))
  ·

    intro n hn a b
    have h := GlobalTheory.T.weil_pairing_tensor_torsion_eq_prod_components R hB D D' W T F N N' ν ν' n hn (P n a) (P n b) _ _ (hP n a) (hP n b)
      (fun i j => ζ n ^ ((e a i).1 ⬝ᵥ (e b j).2 - (e a i).2 ⬝ᵥ (e b j).1)) (fun i j => hweil n hn (e a i) (e b j))
    have key : (∏ i, ∏ j, (ζ n ^ ((e a i).1 ⬝ᵥ (e b j).2 - (e a i).2 ⬝ᵥ (e b j).1)) ^ (W + W.transpose) i j) =
        ζ n ^ Dm.EF a b := by
      rw [hEF a b, zpow_sum_tens]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_sum_tens]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← zpow_mul, mul_comm ((W + W.transpose) i j)]
    beta_reduce at h
    rwa [key] at h
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) ∧ (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) := by
  first | exact @GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data | exact GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data | (intros; apply GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data <;> assumption)
end
