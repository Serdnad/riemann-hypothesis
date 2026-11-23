module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle114
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle174
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisSectionsModK
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedFibreSplitOfArcDataFiniteExtension
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
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem Clos.exists_core_test_of_geoTest : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∃ (τ : ex.core.Test y) (e : pullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j) ≅ t.mod.Φ.G.left), e.hom ≫ t.mod.Φ.G.hom = pullback.snd _ _ ∧ e.hom ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm hbig
  have hin := GlobalTheory.T.testModel_maps_into_openPart hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig
  have hrange : Set.range (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⊆ Set.range Q.G.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hin (Set.mem_univ x)
  let f' : t.u.G.left ⟶ Q.G.toScheme := IsOpenImmersion.lift Q.G.ι _ hrange
  have hf' : f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨-, hloc, hinj, -⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ t.u
  obtain ⟨-, -, hsm, -, hsplit⟩ := GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ t.u
  have hgen := t.u.U.gen_hom
  have g1 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ρ.P.A (c.yK ≫ Q.u₀)
      (tm.φ ≫ pullback.fst ρ.P.A.hom Q.u₀) :=
    ((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr
      ((Category.id_comp _).trans c.yK_u.symm) tm.φ_fst.symm
  have g2 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ((Over.pullback Q.u₀).obj ρ.P.A) c.yK tm.φ :=
    (isGrpPullback_pullback ρ.P.A Q.u₀).cancel g1 tm.φ_snd
  let τ : ex.core.Test y :=
    { V := t.u.V
      complete := t.u.complete
      j := t.u.j
      j_inj := hinj
      j_loc := hloc
      y₀ := c.yV
      fac := c.fac
      H := t.u.G
      smooth := hsm
      sep := t.u.U.separated
      qc := t.u.semi.quasiCompact
      split := hsplit
      f := f'
      f_over := by
        change f' ≫ Q.G.ι ≫ Q.P.hom = _
        rw [← Category.assoc, hf', Category.assoc]
        exact tm.f_over
      yK := c.yK
      yK_fac := c.yK_fac
      φ := tm.φ
      φ_cart := g2
      φ_f := by
        change tm.φ ≫ ex.a = pullback.fst t.u.G.hom (jK t.u.V) ≫ f'
        rw [← cancel_mono Q.G.ι, Category.assoc, ex.a_eq, Category.assoc, hf']
        exact tm.φ_f
      imm := GlobalTheory.T.isClosedImmersion_testSpecialFibre_openPart hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig f' hf'
      lift := by
        intro b hb
        change Sp (OO p) ⟶ Q.G.toScheme at b
        obtain ⟨c', h1, h2⟩ := GlobalTheory.T.exists_lift_integralPoint_closure_testModel hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (b ≫ Q.G.ι)
          ((Category.assoc _ _ _).trans hb) (by
            intro x _
            change (b ≫ Q.G.ι) x ∈ Q.G
            rw [Scheme.Hom.comp_apply]
            exact (b x).2)
        refine ⟨c', h1, ?_⟩
        change c' ≫ f' = b
        rw [← cancel_mono Q.G.ι, Category.assoc, hf']
        exact h2 }
  have hc : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  refine ⟨τ, hc.isoPullback.symm, hc.isoPullback_inv_snd, ?_⟩
  change hc.isoPullback.inv ≫ _ = pullback.fst t.u.G.hom (rPt p ≫ spMap t.u.j) ≫ f' ≫ Q.G.ι
  rw [hf', ← Category.assoc, hc.isoPullback_inv_fst]

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TorsionVanish

theorem form_vanishes_of_torsion : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ v, Crd (Φ.H 1) F x.left v ∧ MvPolynomial.eval v Pf = 0) → ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, MvPolynomial.eval v Pf = 0) := by
  intro L1 L2 k _ _ Φ g N N' q J _ cls F π hBig hGood hg hN' d Pf hd hPf hx v hv
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · obtain ⟨v0, -, hv0⟩ := hx 1 (one_pow _)
    have hC : Pf = MvPolynomial.C (Pf.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hPf.totalDegree_le)
    rw [hC] at hv0 ⊢
    simpa using hv0
  obtain ⟨φ, -, hsupp, hval⟩ := GlobalTheory.ZH.FormSec.exists_formSec k Φ J F d Pf hPf
  obtain ⟨hpart, hfin, -, hsum⟩ := GlobalTheory.ZH.WtPart.weight_parts k Φ d
  obtain ⟨-, -, hsep⟩ := GlobalTheory.exists_basis_unique_min_and_sums_separated Φ.E.X q hGood.pos _ g N N'
    (N ^ g * g.factorial) rfl (by omega) hBig.lll hBig.sep
  have hdist : ∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + N' • w) → α = β := by
    rintro α hα β hβ ⟨w, hw⟩
    obtain ⟨a, ha, rfl⟩ := hsupp α hα
    obtain ⟨b, hb, rfl⟩ := hsupp β hβ
    have h0 : w = 0 := hsep d a b hd
      (fun j => by obtain ⟨i, hi⟩ := ha j; exact (hGood.supp i _ hi).1)
      (fun j => by obtain ⟨i, hi⟩ := hb j; exact (hGood.supp i _ hi).1) w hw
    rw [hw, h0, smul_zero, add_zero]
  have htor : ∀ x : Φ.Pt, x ^ N' = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ := fun x hx1 => by
    obtain ⟨v0, hc, h0⟩ := hx x hx1
    exact (hval x v0 hc).1 h0
  choose ψ hψ using hpart φ
  have hψ0 : ∀ α l, (ψ α).f l = 0 := fun α =>
    GlobalTheory.PureZero.pure_eq_zero_of_vanishing_on_torsion L1 L2 k Φ g N N' d π hBig hN' (by omega) hd1 hd α (ψ α) (hψ α).1
      (GlobalTheory.T.part_vanishes_on_torus_torsion_fourier k Φ d N' hN' φ hdist htor α (ψ α) (hψ α))
  have hφ0 : ∀ l, φ.f l = 0 := fun l => by
    rw [hsum φ (hfin φ).toFinset ψ (by simp) (fun α _ => hψ α) l]
    exact Finset.sum_eq_zero fun α _ => hψ0 α l
  obtain ⟨x, hxp, hc⟩ := hv
  refine (hval (Over.homMk x hxp) v hc).2 fun h => ?_
  have hb : Out.nonzeroLocus φ = ⊥ := by
    simp [Out.nonzeroLocus, hφ0]
  rw [hb] at h
  obtain ⟨p⟩ : Nonempty (Sp k) := (inferInstance : Nonempty (PrimeSpectrum k))
  exact h (Set.mem_univ p)

end GlobalTheory.ZH.TorsionVanish
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  first | exact @GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero | exact GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero | (intros; apply GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.OneBasis.AdaptedFamily

theorem exists_min_on {X : Type} {Q : X → ℤ} (h : ∀ x, 0 ≤ Q x) {s : Set X} (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, Q x ≤ Q y := by
  obtain ⟨x, hx, hm⟩ := (wellFounded_lt (α := ℕ)).has_min ((fun x => (Q x).toNat) '' s) (hs.image _)
  obtain ⟨x, hx, rfl⟩ := hx
  refine ⟨x, hx, fun y hy => ?_⟩
  have h₁ : ¬ (Q y).toNat < (Q x).toNat := hm _ ⟨y, hy, rfl⟩
  have h₂ := h x
  have h₃ := h y
  omega

theorem main : LL → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α), AdFam D Q k cls mu f ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (i : Fin r), ∃ s : Fam D.toPre F k, GlobalTheory.ZH.FamOf D.toPre F (f i) s := by
  classical
  intro hL V _ _ _ ϖ hϖ D Q hQ k hk
  have hQ0 : ∀ χ, 0 ≤ Q χ := fun χ => by
    by_cases h : χ = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · have := QForm.Q_pos hϖ D hQ h; omega
  let C := D.toPre.X ⧸ FamFree.multiples D.toPre k
  have hc : Nat.card C = k ^ Module.finrank ℤ D.toPre.X := AddSubgroup.index_range_nsmul D.toPre.X k
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite C
  let e : Fin (Fintype.card (C × Fin (k ^ D.toPre.P.g))) ≃ C × Fin (k ^ D.toPre.P.g) := (Fintype.equivFin _).symm
  choose rep hrep hmin using fun c : C => exists_min_on hQ0
    (s := {α | (QuotientAddGroup.mk α : C) = c}) ⟨c.out, c.out_eq⟩
  have hQmin : ∀ c z, Q (rep c) ≤ Q (rep c + k • z) := fun c m =>
    hmin c _ (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, rfl⟩).symm.trans (hrep c))
  choose b hb using fun c => AdaptedBasis.exists_isBasisB hL.2.1.secTwist D.toPre hk (rep c)
  choose Φ f hΦ hf hz using fun c m =>
    AdaptedBasis.integralFamily_of_min hL.1.globalFns hϖ hQ hk (rep c) (b c m) (hQmin c)
  have inj : ∀ c c', rep c = rep c' → c = c' := fun c c' h => (hrep c).symm.trans (by rw [h]; exact hrep c')
  let ε : ∀ i₀, {i // rep (e i).1 = rep (e i₀).1} ≃ Fin (k ^ D.toPre.P.g) := fun i₀ =>
    { toFun := fun i => (e i.1).2
      invFun := fun m => ⟨e.symm ((e i₀).1, m), by rw [Equiv.apply_symm_apply]⟩
      left_inv := fun i => Subtype.ext (e.symm_apply_eq.2 (Prod.ext (inj _ _ i.2).symm rfl))
      right_inv := fun m => by simp }
  refine ⟨_, fun i => rep (e i).1, k ^ D.toPre.P.g, fun i => f (e i).1 (e i).2,
    ⟨⟨fun i => hQmin _, fun i i' ⟨m, hm⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩, fun i => ⟨_, hΦ _ _⟩, fun i => hz _ _,
      fun i₀ => ?_⟩, fun F _ _ i => FamBaseChange.main hL.1.globalFns V _ D k _ _ (hΦ _ _) F⟩
  · exact congrArg rep ((hrep _).symm.trans (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, hm.symm⟩).symm.trans (hrep _)))
  · obtain ⟨m, hm⟩ := (FamFree.mk_eq_mk_iff _ _).1 (hrep (QuotientAddGroup.mk α))
    refine ⟨e.symm (QuotientAddGroup.mk α, ⟨0, by positivity⟩), m, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hm.symm
  · exact (Nat.card_congr (ε i₀)).trans (Nat.card_fin _)
  · refine AdaptedBasis.isBasisB_reindex (ε i₀) (hb (e i₀).1) fun i => ?_
    have key : ∀ c c' m, c = c' → f c m (rep c') = b c' m := by
      rintro c _ m rfl; exact hf c m
    exact key _ _ _ (inj _ _ i.2)

end GlobalTheory.OneBasis.AdaptedFamily
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Degen.PolyStepLocal

theorem nilpotent_ker {R : Type} [CommRing R] (I : Ideal R) {n : ℕ} (h : I ^ n ≤ I ^ (0 + 1)) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨n, ?_⟩
  have hk : RingHom.ker (Ideal.Quotient.factor h) ≤ I.map (Ideal.Quotient.mk (I ^ n)) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hx
    exact Ideal.mem_map_of_mem _ hx
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  refine (Ideal.pow_right_mono hk n).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem exists_h1Zero_pw (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB)
    (hs : VeryAmpleBy f H s) : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → FirstCohomologyVanishes (GlobalTheory.AbLaw.pw H t) := by
  have isLB_pw {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (t : ℤ) :
      (AbLaw.pw L t).IsLB := by
    refine ⟨hL.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hL.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hL.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.serre_vanishing_very_ample.1 R X f H m s hH hs H hH
  refine ⟨t₀.toNat + 1, fun t ht => ?_⟩
  obtain ⟨w, hw⟩ := GlobalTheory.Algebraise.lbIso_tw hH ((t : ℤ) - 1)
  have h := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH hH _).cover (isLB_pw hH _) w hw (ht₀ _ (by omega))
  rwa [sub_add_cancel] at h

theorem exists_form_lift {σ R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : Function.Surjective g)
    {F : MvPolynomial σ R'} {t : ℕ} (hF : F.IsHomogeneous t) :
    ∃ G : MvPolynomial σ R, G.IsHomogeneous t ∧ MvPolynomial.map g G = F := by
  obtain ⟨G, rfl⟩ := MvPolynomial.map_surjective g hg F
  refine ⟨MvPolynomial.homogeneousComponent t G, MvPolynomial.homogeneousComponent_isHomogeneous t G, ?_⟩
  ext d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
  split_ifs with h
  · rw [MvPolynomial.coeff_map]
  · rw [map_zero, hF.coeff_eq_zero h]

theorem cst_comp_spec {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
    (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
    AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom g)) U = (AbLaw.cst p U).comp g := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem exists_pull_tower {σ R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (H : ∀ e, LB (Y e).left) (hH : ∀ e, (H e).IsLB) (s : ∀ e, σ → LB.Sec (H e))
    (hs : ∀ e, GlobalTheory.MorAlg.IsPull (β e) (s (e + 1)) (s e)) (e : ℕ) :
    ∃ j₀ : (Y 0).left ⟶ (Y (e + 1)).left, IsPullback j₀ (Y 0).hom (Y (e + 1)).hom (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega) : I ^ (e + 1 + 1) ≤ I ^ (0 + 1))))) ∧
      GlobalTheory.MorAlg.IsPull j₀ (s (e + 1)) (s 0) := by
  induction e with
  | zero => exact ⟨β 0, hβ 0, hs 0⟩
  | succ e ih =>
    obtain ⟨j₀, hj, hr⟩ := ih
    refine ⟨j₀ ≫ β (e + 1), ?_, GlobalTheory.MorAlg.IsPull.comp (hH _) (hH _) (hH _) (hs (e + 1)) hr⟩
    convert hj.paste_horiz (hβ (e + 1)) using 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp]

end GlobalTheory.Degen.PolyStepLocal


open GlobalTheory.Degen.PolyStepLocal in
theorem GlobalTheory.Degen.exists_form_correction_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k'))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick R I (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, AddMonoidAlgebra.coeff G d ∈ I ^ (e + 1)) ∧ (∀ k : (H (e + 1)).ι, MvPolynomial.eval₂Hom (cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) ((H (e + 1)).U k)) (fun j => (s (e + 1) j).f k) (F - G) = 0) := by
  intro R _ _ _ I hI Y β hβ hflat H v hH n s hs hva
  have hle : ∀ r ∈ I ^ (0 + 1), IsLocalRing.residue R r = 0 := fun r hr => by
    rw [zero_add, pow_one] at hr
    exact (IsLocalRing.residue_eq_zero_iff r).2 (IsLocalRing.le_maximalIdeal hI hr)
  let φ : R ⧸ I ^ (0 + 1) →+* IsLocalRing.ResidueField R := Ideal.Quotient.lift _ (IsLocalRing.residue R) hle
  have hφ : Function.Surjective φ := Ideal.Quotient.lift_surjective_of_surjective _ hle IsLocalRing.residue_surjective
  have hP := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom φ))
  set π := pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom φ))
  set f₀ := pullback.snd (Y 0).hom (Spec.map (CommRingCat.ofHom φ))
  have hL := LB.isLB_pull (hH 0).1 π
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.MorAlg.exists_isPull π (hH 0).1 (s 0)
  have hva₀ : VeryAmpleBy f₀ ((H 0).pull π) s₀ := by
    obtain ⟨w, hw, c⟩ := hs₀
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull _ _ (Y 0).hom (H 0) n (s 0) (hH 0).1 hva _ φ _ f₀ π hP.w ?_ _ w
      s₀ hL hw c
    have : pullback.lift π f₀ hP.w = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.id_comp]
      · rw [pullback.lift_snd, Category.id_comp]
    rw [this]
    infer_instance
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.Degen.PolyStepLocal.exists_h1Zero_pw _ _ f₀ _ n s₀ hL hva₀
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.T.serre_vanishing_very_ample.2 _ _ f₀ _ n s₀ hL hva₀
  refine ⟨max t₁ t₂, fun t ht e F hF hF0 => ?_⟩
  obtain ⟨j₀, hj, w, hw', hr⟩ := GlobalTheory.Degen.PolyStepLocal.exists_pull_tower _ Y β hβ H (fun e => (hH e).1) s
    (fun e => ⟨v e, (hH e).2, hs e⟩) e
  have hvae : VeryAmpleBy (Y (e + 1)).hom (H (e + 1)) (s (e + 1)) :=
    GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _) (GlobalTheory.Degen.PolyStepLocal.nilpotent_ker I _) _ _ _ _ j₀ hj
      _ _ w n _ _ (hH _).1 (hH _).1 hw' hr hva
  obtain ⟨w₀, hw₀, c₀⟩ := GlobalTheory.MorAlg.IsPull.comp (hH (e + 1)).1 (hH 0).1 hL ⟨w, hw', hr⟩ hs₀
  have hP₀ := hP.paste_horiz hj
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hP₀
  have hne : I ^ (e + 1 + 1) ≠ ⊤ := fun h => hI (top_unique (h ▸ Ideal.pow_le_self (by omega)))
  have : Nontrivial (R ⧸ I ^ (e + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  have : IsLocalRing (R ⧸ I ^ (e + 1 + 1)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have c₁ : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  obtain ⟨G₀, hG₀, hc, hz⟩ := GlobalTheory.T.exists_form_correction_of_vanishing_after_baseChange _ _ (Y (e + 1)).hom (hflat _) _ n _ (hH _).1 hvae _ _
    (hφ.comp (Ideal.Quotient.factor_surjective _)) _ _ _ hP₀ _ w₀ s₀ hL hw₀ c₀ t (ht₁ t (le_of_max_le_left ht))
    (ht₂ t (le_of_max_le_right ht)) _ _ _ (β e) (Y e).hom (hβ e) _ (v e) (s e) (hH e).1 (hH e).2 (hs e)
    (MvPolynomial.map (Ideal.Quotient.mk _) F) (hF.map _) (fun k => by
      rw [MvPolynomial.eval₂Hom_map_hom, ← GlobalTheory.Degen.PolyStepLocal.cst_comp_spec, Category.assoc]
      exact (congrArg (fun p => MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p ((H e).U k)) (fun j => (s e j).f k) F) c₁).trans
        (hF0 k))
  obtain ⟨G, hG, rfl⟩ := GlobalTheory.Degen.PolyStepLocal.exists_form_lift _ Ideal.Quotient.mk_surjective hG₀
  refine ⟨G, hG, fun d => ?_, fun k => ?_⟩
  · have h := hc d
    rw [MvPolynomial.coeff_map, Ideal.Quotient.factor_mk] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · have h := hz k
    rw [← map_sub, MvPolynomial.eval₂Hom_map_hom, ← GlobalTheory.Degen.PolyStepLocal.cst_comp_spec] at h
    exact h
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.potentialSemiAbelianReduction_of_retract : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (B Q : Over (Sp K)) [GrpObj B] [GrpObj Q] (i : B ⟶ Q) (r : Q ⟶ B), IsMonHom i → IsMonHom r → i ≫ r = 𝟙 B → PotModel V K Q (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_semiAbelian_of_retract | exact GlobalTheory.SS.potModel_semiAbelian_of_retract | (intros; apply GlobalTheory.SS.potModel_semiAbelian_of_retract <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.kTriv_of_kTriv_nonemptyOpen_normal_charZero : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → (∀ n : ℕ, n ≠ 0 → (n : Γ(S, ⊤)) ≠ 0) → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L), IsAbelianScheme G → Out.RelAmple G L.L → Out.KTriv ((Over.pullback U.ι).obj G) (L.L.pull (pullback.fst G.hom U.ι)) → Out.KTriv G L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_open_normal | exact GlobalTheory.KTrivSpread.kTriv_of_open_normal | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_open_normal <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.closedFibre_split_of_arcData_finite_extension : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : O' →+* V) (u : V), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (χ : Sp V ⟶ Y.X) (y : Sp (FractionRing V) ⟶ Xo.XF c), y ≫ Y.j = jK V ≫ χ → ∀ (t : SAB H (Sp V)) (_ : SABMap t Y.t χ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V' → ∀ g : V →+* V', Function.Injective g → g.Finite → Y.HasArcData a (IsLocalRing.maximalIdeal V') (g.comp f) (g u) (spMap g ≫ χ) → SplitOver t.G (IsLocalRing.maximalIdeal V) := by
  first | exact @GlobalTheory.SplitAtTrait.splitOver_of_hasArcData | exact GlobalTheory.SplitAtTrait.splitOver_of_hasArcData | (intros; apply GlobalTheory.SplitAtTrait.splitOver_of_hasArcData <;> assumption)
end
