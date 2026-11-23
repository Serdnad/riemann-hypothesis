module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle066
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle024
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle067
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle025
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PotentialBoundedPshBoth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lat_isGenAt_of_proper_birational : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t :=
  @PositivityTheory.Xgn.line_lattice_proper_pushdown

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem kappa_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type)
    [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (M : ℕ) (f g : MRing ι) (dg : K → ℕ)
    (κ : (F →+* ℂ) → ℝ), OverInt y φ → 0 < M → IsMultiHomog g dg → g ∉ mCoordIdeal y → IsConjInvariantH A →
    (∀ σ, 0 < κ σ) → (∀ σ z, PtOver y φ σ z → ‖evC z f‖ = (κ σ * A.h z) ^ M * ‖evC z g‖) →
    ∀ σ, κ (ComplexEmbedding.conjugate σ) = κ σ := by
  intro K _ ι _ Ω _ F _ _ y φ A M f g dg κ hO hM hg hgy hA hκ hN σ
  obtain ⟨z, hz, hgz⟩ := GlobalTheory.T.exists_complex_point_nonvanishing K ι Ω F y φ σ g dg hO hg hgy
  have h1 := hN σ z hz
  have h2 := hN _ _ (ptOver_conj K ι Ω F y φ σ z hz)
  rw [evC_conj, evC_conj, hA z, RCLike.norm_conj, RCLike.norm_conj] at h2
  have hgn : ‖evC z g‖ ≠ 0 := norm_ne_zero_iff.2 hgz
  have hh : 0 < A.h z := A.pos z hz.1.1
  have h3 : (κ (ComplexEmbedding.conjugate σ) * A.h z) ^ M = (κ σ * A.h z) ^ M :=
    mul_right_cancel₀ hgn (h2.symm.trans h1)
  have h4 := (pow_left_inj₀ (mul_pos (hκ _) hh).le (mul_pos (hκ _) hh).le hM.ne').1 h3
  exact mul_right_cancel₀ hh.ne' h4

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.normal_cpt_iff_normal_scheme : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ IsNormalScheme X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal | exact GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tw_funct : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) :=
  @PositivityTheory.HtPt.Twfunct.tw_funct

end GlobalTheory.CompanionTheory.Ar.HT
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem prod_ofFn_lieModel_pt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∀ {n : ℕ} (f : Fin n → E), (List.ofFn fun j => M.pt (f j)).prod = M.pt (∑ j, f j)
  | 0, f => by simp [M.pt_zero]
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_lieModel_pt M, Fin.sum_univ_succ, M.add]

theorem isComb_unit_row : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F]
    (x : Sp F ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)), (∀ i, IsTanAt G x (v i)) →
    ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) := by
  intro S G _ _ F _ x n v hv i
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  choose e he using fun j => M.onto (v j) (hv j)
  refine ⟨fun j => M.pt ((1 : Matrix (Fin n) (Fin n) F) i j • e j), fun j => ?_, ?_⟩
  · rw [M.smul, he]
  · rw [prod_ofFn_lieModel_pt M, ← he i]
    congr 1
    simp [Matrix.one_apply, ite_smul]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.chart_unit_basic_open : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis | exact GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.regAt_chart_localization : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation | exact GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation | (intros; apply GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.regAt_le_iff_specializes : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes | exact GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem lat_twist_globally_generated : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∃ (d n : ℕ) (z : Fin n → E), ∀ c (p : Cpt M.ξ), InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k) :=
  PositivityTheory.HtPt.Ma.serre

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

theorem comp_act (𝓗 : HodgeLat L ρ bar r) {σ : E →+* Ω} {φ : Module.Dual Ω V}
    (h : ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ) (a : 𝓞 E) : φ ∘ₗ ρ (bar a) = σ (a : E) • φ := by
  have h1 := (HT.LatBasic.mem_eigSp.mp h) a
  rw [𝓗.act_inr] at h1
  exact congrArg Prod.snd h1

theorem comp_eigProj (𝓗 : HodgeLat L ρ bar r) {σ σ' : E →+* Ω}
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) {φ : Module.Dual Ω V}
    (h : ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ) : φ ∘ₗ HT.eigProj ρ σ' = φ := by
  have key : ∀ b : 𝓞 E, φ ∘ₗ ρ b = σ' (b : E) • φ := by
    intro b
    have h1 := comp_act 𝓗 h (bar b)
    rw [hb b] at h1
    rw [h1, hσ b]
  have hsum : ∑ k, σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    have h1 := congrArg σ' (HT.LatBasic.sum_dualInt_mul (E := E))

    rw [map_sum, map_one] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, NumberField.integralBasis_apply]
  unfold HT.eigProj
  ext x
  have hk : ∀ k, φ ((σ' (HT.dualInt E k) • ρ (RingOfIntegers.basis E k)) x) =
      σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) * φ x := by
    intro k
    have e := LinearMap.congr_fun (key (RingOfIntegers.basis E k)) x
    rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at e
    rw [LinearMap.smul_apply, map_smul, e, smul_eq_mul, mul_assoc]

  rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  simp_rw [hk]
  rw [← Finset.sum_mul, hsum, one_mul]

end

theorem adapted_span : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω]
    (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q r : ℕ) (𝓗 : HodgeLat L ρ bar r)
    (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V),
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent Ω v →
    Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w →
    Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u →
    LinearIndependent Ω u ∧ Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ ∧
      ∀ φ : Module.Dual Ω V, ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ → φ ∘ₗ HT.eigProj ρ σ' = φ := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q r 𝓗 σ σ' v w u hσ hb hv hvs hw hws hu
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hz : ∀ j, (u (Fin.natAdd p j)).1 = 0 := fun j => (hu3 j).1
  have hz2 : ∀ j j', (u (Fin.natAdd p j)).2 (w j') = if j = j' then 1 else 0 := fun j => (hu3 j).2
  have hli : LinearIndependent Ω u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    have h1 : ∀ i, g (Fin.castAdd q i) = 0 := by
      have hf := congrArg Prod.fst hg
      simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hu2, hz] at hf
      exact Fintype.linearIndependent_iff.mp hv _ hf
    have h2 : ∀ j, g (Fin.natAdd p j) = 0 := by
      intro j'
      have hs := congrArg (fun y : V × Module.Dual Ω V => y.2 (w j')) hg
      simpa [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, h1, hz2] using hs
    intro i
    exact Fin.addCases h1 h2 i
  have hspan : Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hu1 i
    · intro y hy
      have hy1 : y.1 ∈ HT.eigSp ρ σ := by
        rw [HT.LatBasic.mem_eigSp]
        intro a
        have h1 := congrArg Prod.fst ((HT.LatBasic.mem_eigSp.mp hy) a)
        rw [𝓗.act_fst] at h1
        exact h1
      rw [← hvs, Submodule.mem_span_range_iff_exists_fun] at hy1
      obtain ⟨c, hc⟩ := hy1
      set y' := y - ∑ i, c i • u (Fin.castAdd q i) with hy'
      have hy'mem : y' ∈ HT.eigSp 𝓗.ρH σ :=
        Submodule.sub_mem _ hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hu1 _))
      have hy'1 : y'.1 = 0 := by
        simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy', hu2, hc]
      set χ := y'.2 - ∑ j, y'.2 (w j) • (u (Fin.natAdd p j)).2 with hχ
      have hχmem : ((0 : V), χ) ∈ HT.eigSp 𝓗.ρH σ := by
        have e : ((0 : V), χ) = y' - ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
          refine Prod.ext ?_ ?_
          · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy'1, hz]
          · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hχ]
        rw [e]
        exact Submodule.sub_mem _ hy'mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu1 _))
      have hχw : ∀ j', χ (w j') = 0 := by
        intro j'
        simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hχ, hz2]
      have hχker : HT.eigSp ρ σ' ≤ LinearMap.ker χ := by
        rw [← hws, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact hχw j
      have hχ0 : χ = 0 := by
        have h2 := comp_eigProj 𝓗 hσ hb hχmem
        ext x
        rw [← h2, LinearMap.comp_apply, LinearMap.zero_apply]
        exact LinearMap.mem_ker.mp (hχker (HT.LatBasic.eigProj_mem ρ σ' x))
      have hy2 : y'.2 = ∑ j, y'.2 (w j) • (u (Fin.natAdd p j)).2 := sub_eq_zero.mp hχ0
      have hT : y' = ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy'1, hz]
        · simpa [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] using hy2
      have hyeq : y = ∑ i, c i • u (Fin.castAdd q i) + ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
        rw [← hT, hy']
        abel
      rw [hyeq]
      exact Submodule.add_mem _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  exact ⟨hli, hspan, fun φ hφ => comp_eigProj 𝓗 hσ hb hφ⟩

end GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan
end
end

section

open GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.potential_bounded_psh_both : ∀ (e : ℕ) (σ : Type) (S : PB.AnSys e σ) (a : σ), (∀ t, ReciprocityTheory.AnForm.M.IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ ReciprocityTheory.AnForm.M.IsPsh S.A (S.potT a t)) → ∃ C : ℝ, ∀ t, 0 < t → t ≤ S.t₀ → ∀ x, |S.phT a t x| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded | exact GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC

open GlobalTheory.CompanionTheory.Ar.TorusModel

theorem pt_ext {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap e) φ) {T : Over (Sp L')} (u v : T ⟶ G')
    (huv : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext huv (by rw [Over.w u, Over.w v]))

theorem isTanAt_comp {S : Scheme.{0}} {R : Type} [CommRing R] {H G : Over S} [GrpObj H] [GrpObj G] (i : H ⟶ G)
    [IsMonHom i] (x : Sp R ⟶ S) (v : epsAt x ⟶ H) (hv : IsTanAt H x v) : IsTanAt G x (v ≫ i) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem dualMap_cast {L L' : Type} [Field L] [Field L'] (e : L →+* L') (n : ℤ) :
    dualMap e (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (n : L)) =
      TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (n : L') := by
  ext <;> simp [dualMap]

theorem base_comm {L L' : Type} [Field L] [Field L'] (e : L →+* L') :
    spMap (dualMap e) ≫ Spec.map (CommRingCat.ofHom (algebraMap L (DualNumber L))) ≫ 𝟙 (Sp L) =
      (Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e := by
  simp only [Category.comp_id, Category.id_comp]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem push_eq {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] (φ : G'.left ⟶ G.left) {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (i : splitTorus (Sp L) X ⟶ G) (i' : splitTorus (Sp L') X' ⟶ G') (κ : X ≃+ X')
    (hκ : ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Sp L') (t' : Over.mk a ⟶ splitTorus (Sp L') X')
      (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X), (∀ χ, charVal t χ = charVal t' (κ χ)) →
        (t' ≫ i').left ≫ φ = (t ≫ i).left)
    (MT : LieModel (splitTorus (Sp L) X) (𝟙 _) (X →+ L)) (hMT : IsCocharLie MT)
    (MT' : LieModel (splitTorus (Sp L') X') (𝟙 _) (X' →+ L')) (hMT' : IsCocharLie MT') (δ : X →+ ℤ) :
    (MT'.pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom)) ≫ i').left ≫ φ =
      spMap (dualMap e) ≫ (MT.pt ((Int.castAddHom L).comp δ) ≫ i).left := by
  set c := (Int.castAddHom L).comp δ with hc
  have hw : spMap (dualMap e) ≫ (MT.pt c).left ≫ (splitTorus (Sp L) X).hom =
      (Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e := by
    rw [Over.w (MT.pt c)]
    exact base_comm e
  let t : Over.mk ((Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e) ⟶
      splitTorus (Sp L) X := Over.homMk (spMap (dualMap e) ≫ (MT.pt c).left) (by simpa using hw)
  have h := hκ (DualNumber L') _ (MT'.pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom))) t (fun χ => by
    rw [charVal_comp (dualMap e) (MT.pt c) t rfl χ, hMT c χ, hMT' _ (κ χ)]
    simpa [hc] using dualMap_cast e (δ χ))
  rw [h]
  simp [t]

theorem cochars_baseChange : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (τ : TorusExtension G) (τ' : TorusExtension G'), IsGrpPullback G' G (spMap e) φ → GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e τ τ' φ → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → ∀ I : AddSubgroup V, (letI := τ.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L), IsCocharLie MT ∧ ∀ x, x ∈ I ↔ ∃ δ : τ.X →+ ℤ, MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i) → (letI := τ'.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L') τ'.X) (𝟙 _) (τ'.X →+ L'), IsCocharLie MT ∧ ∀ x, x ∈ I.map j ↔ ∃ δ : τ'.X →+ ℤ, MV'.pt x = MT.pt ((Int.castAddHom L').comp δ) ≫ τ'.i) := by
  intro L L' _ _ e G G' _ _ φ τ τ' hP hTO V V' _ _ _ _ MV MV' j hj I hI
  letI := τ.addCommGroup
  letI := τ'.addCommGroup
  obtain ⟨κ, hκ⟩ := hTO
  obtain ⟨MT, hMT, hI⟩ := hI
  have hM' := isCocharLie_lieModel (X := τ'.X) (𝟙 (Sp L'))
  have hi := τ.i_hom
  have hp := fun δ => push_eq e φ τ.i τ'.i κ hκ MT hMT (lieModel (𝟙 (Sp L'))) hM' δ
  have hfw : ∀ (x : V) (δ : τ.X →+ ℤ), MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i →
      MV'.pt (j x) = (lieModel (𝟙 (Sp L'))).pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom)) ≫ τ'.i := by
    intro x δ hx
    refine pt_ext e hP _ _ ?_
    rw [hj x, hx, hp δ]
  refine ⟨lieModel (𝟙 (Sp L')), hM', fun x' => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨δ, hδ⟩ := (hI x).1 hx
    exact ⟨_, hfw x δ hδ⟩
  · rintro ⟨δ', hδ'⟩
    set δ : τ.X →+ ℤ := δ'.comp κ.toAddMonoidHom with hδ
    obtain ⟨x, hx⟩ := MV.onto _ (isTanAt_comp τ.i _ _ (MT.tan ((Int.castAddHom L).comp δ)))
    refine ⟨x, (hI x).2 ⟨δ, hx⟩, MV'.inj ?_⟩
    rw [hfw x δ hx, hδ', hδ]
    congr 3
    ext χ
    simp

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC
end
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.semiabelian_adic_torsion_four : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.tw_funct | exact GlobalTheory.CompanionTheory.Ar.HT.tw_funct | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.tw_funct <;> assumption)

end
end
