module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle203
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle172
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle258
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjoint
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle072
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle225
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle264
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle265
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle266
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.interior_point_lattice_data : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z → Top.Given → ∀ (A₀ : Type) (v : A₀ → (epsAt z ⟶ 𝔐.t.G)), (∀ i, IsTanAt 𝔐.t.G z (v i)) → ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (x : A₀ → Fin g → ℂ), FibreLatVec 𝔐.t z R x v ∧ (∀ i j, HodgeIP 𝔐.t.G 𝔐.t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j))) ∧ ∀ σ, 𝔐.LabVal z id σ → ∀ s, Module.finrank ℂ (eigSp R.B (σ s)) = labelRk D s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_coords_of_generic_point : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Spec (CommRingCat.of Ω) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (bd : Ideal (MRing J)), Nonempty K ∧ (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PeriodIndep

section Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem disjoint_sup_biSup {α I : Type} [CompleteLattice α] [IsModularLattice α] {t : I → α} (hind : iSupIndep t)
    (a b : I) : Disjoint (t a ⊔ t b) (⨆ s ∈ {s | s ≠ a ∧ s ≠ b}, t s) := by
  by_cases hab : a = b
  · subst hab
    rw [sup_idem]
    exact hind.disjoint_biSup fun h => h.1 rfl
  · refine Disjoint.disjoint_sup_left_of_disjoint_sup_right (hind.disjoint_biSup fun h => h.2 rfl) ?_
    have h1 : t b ≤ ⨆ j, ⨆ (_ : j ≠ a), t j :=
      le_iSup₂_of_le (f := fun j (_ : j ≠ a) => t j) b (fun h => hab h.symm) le_rfl
    have h2 : (⨆ s ∈ {s | s ≠ a ∧ s ≠ b}, t s) ≤ ⨆ j, ⨆ (_ : j ≠ a), t j :=
      iSup₂_le fun s hs => le_iSup₂_of_le (f := fun j (_ : j ≠ a) => t j) s hs.1 le_rfl
    exact (hind a).mono_right (sup_le h1 h2)

theorem exists_dual_sup (𝔐 : HodgeCpt Y S y) (hind : iSupIndep 𝔐.Vgen) (q : Cpt 𝔐.ξ)
    (hV : ∀ s, 𝔐.V s q = 𝔐.dR s q) (hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q) (a b : CMType H ⊕ CMType H) {N : ℕ}
    (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b))
    (hfr : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb q) :
    ∃ π : Fin N → Module.Dual Ω 𝔐.Li, (∀ j l, π j (bb l : 𝔐.Li) = if j = l then 1 else 0) ∧
      ∀ j, ∀ e ∈ 𝔐.M.lat q, π j e ∈ regAt 𝔐.ξ q := by
  classical
  obtain ⟨hli, hsp⟩ := hfr
  obtain ⟨W, hW, hc⟩ := (disjoint_sup_biSup hind a b).symm.exists_isCompl
  let pr : 𝔐.Li →ₗ[Ω] ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := Submodule.projectionOnto _ _ hc.symm
  have hker : LinearMap.ker (Fintype.linearCombination Ω bb) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun m hm => funext fun k => ?_
    exact Fintype.linearIndependent_iff.1 hli m (by rwa [Fintype.linearCombination_apply] at hm) k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hgb : ∀ l, g (bb l) = Pi.single l 1 := fun l => by
    have := LinearMap.congr_fun hg (Pi.single l 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hpr : ∀ x : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b), pr (x : 𝔐.Li) = x := fun x =>
    Submodule.projectionOnto_apply_left hc.symm x
  refine ⟨fun j => (LinearMap.proj j).comp (g.comp pr), fun j k => ?_, fun j e he => ?_⟩
  · simp only [LinearMap.comp_apply, hpr, hgb, LinearMap.proj_apply]
    simp [Pi.single_apply]
  · rw [hlat] at he
    induction he using Submodule.iSup_induction' with
    | mem s' x hx =>
      by_cases e : s' = a ∨ s' = b
      · have hxs : x ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
          rcases e with rfl | rfl
          · exact Submodule.mem_sup_left hx.2
          · exact Submodule.mem_sup_right hx.2
        have hxV : x ∈ 𝔐.V a q ⊔ 𝔐.V b q := by
          rcases e with rfl | rfl
          · exact Submodule.mem_sup_left ((hV _).symm ▸ hx)
          · exact Submodule.mem_sup_right ((hV _).symm ▸ hx)
        have hm : (⟨x, hxs⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) ∈
            Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype q := hxV
        rw [hsp] at hm
        obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
        have e1 : ∀ k, (c' k • bb k) = ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := fun _ => rfl
        have e2 : pr x = ∑ k, ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := by
          rw [show pr x = ⟨x, hxs⟩ from hpr ⟨x, hxs⟩, ← hc']
          exact Finset.sum_congr rfl fun k _ => e1 k

        simp only [LinearMap.comp_apply, e2, map_sum, map_smul, hgb, LinearMap.proj_apply]
        refine sum_mem fun k _ => ?_
        rw [smul_eq_mul]
        refine mul_mem (c' k).2 ?_
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · have hxW : x ∈ W := by
          push Not at e
          exact hW (Submodule.mem_iSup_of_mem s' (Submodule.mem_iSup_of_mem e hx.2))
        have : pr x = 0 := Submodule.projectionOnto_apply_of_mem_right hc.symm hxW
        simp [this]
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy

end Dual

theorem values_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z Vz) (e : Fin N → Vz), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → (∀ k, 𝔐.M.ValAt z ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) (MR.pt (e k))) → LinearIndependent ℂ e := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z h Vz _ _ MR e hfr hval
  classical
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨hV, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, h⟩
    fun r hr => GrNorm.not_inFibre hξ h hr
  obtain ⟨π, hπ, hreg⟩ := exists_dual_sup 𝔐 hind ⟨centre z, h⟩ hV hlat a b bb hfr
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (e k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := GlobalTheory.T.lattice_regular_at_local_point 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z h Vz MR (π j) hξ (hreg j)
    refine ⟨g, fun k => hg (bb k : 𝔐.Li) _ _ (hval k) ?_⟩
    rw [hπ j k]
    split_ifs
    · exact RootHt.ArchB.val_one h
    · exact RootHt.ArchB.val_zero h
  choose g hg using hg
  refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
  have := congrArg (g j) hw

  simpa [map_sum, hg, Finset.sum_ite_eq] using this

end GlobalTheory.CompanionTheory.Ar.PeriodIndep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_interior_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), Function.Injective β → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → ∀ s (i : Fin (labelRk D s)) (t : Ω), ((𝔐.V s).gr (Fl.b s) i).IsGenAt ⟨centre z, 𝔐.all _⟩ t → ∃ ν : ℝ, 0 < ν ∧ ∀ (t' : Ω) (ν' : ℝ), 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) i z t' ν' ↔ ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (t' / t) u ∧ ν' = ‖u‖ * ν := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm | exact GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm | (intros; apply GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameGram

theorem inner_eq_pi_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x y : D.B.carrier) (c c' : Fin D.g → ℂ), D.IsVec a x c → D.IsVec a y c' → ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) : ℂ) = Real.pi * a.herm c' c := by
  intro E _ _ _ H L _ _ D σ a x y c c' hx hy
  obtain ⟨t', m, hP, hA⟩ := GlobalTheory.T.complex_abelian_fibre_ample E H L D σ
  obtain ⟨hab, g, u, Hm, χ, hAH, d₁, d₂⟩ := FrameEx.exists_goodUnif E H _ D.t (emb σ) t' m hP hA
  have hp : IsGrpPullback t'.G D.t.G (emb σ) m.φ := m.cart
  obtain ⟨v, hlift, vA, hvA, hdiff⟩ := hx
  obtain ⟨w, hlift', wA, hwA, hdiff'⟩ := hy
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L)) = emb σ := Category.comp_id _
  let v₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk v.left (by simpa using Over.w v)
  let w₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk w.left (by simpa using Over.w w)
  have hl₀ : (v₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) := hlift
  have hl₁ : (w₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt y).left) := hlift'
  obtain ⟨hL, hvt, hwt, A', _, φ', g', u', Hm', χ', p, q, a', b', hp', hah', ep, eq', dp, dq, hval⟩ :=
    D.fib σ x y v₀ w₀ hl₀ hl₁
  have hp₀ : IsGrpPullback t'.G D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) m.φ :=
    IsGrpPullback.congr hp e.symm rfl
  have hpz : IsGrpPullback A' D.t.G (emb σ) φ' := IsGrpPullback.congr hp' e rfl
  let x₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm v₀
  let y₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm w₀
  have hx₁ : HodgeLin.tanEquiv hp₀ x₁ = v₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have hy₁ : HodgeLin.tanEquiv hp₀ y₁ = w₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have tx₁ : IsTangent x₁ := (HodgeLin.isTangent_iff hp₀ x₁).2 (by rw [hx₁]; exact hvt)
  have ty₁ : IsTangent y₁ := (HodgeLin.isTangent_iff hp₀ y₁).2 (by rw [hy₁]; exact hwt)
  have lx₁ : x₁.left ≫ m.φ = v.left := congrArg (fun r => r.left) hx₁
  have ly₁ : y₁.left ≫ m.φ = w.left := congrArg (fun r => r.left) hy₁
  obtain ⟨cx, hcx, -⟩ := d₁ x₁ tx₁
  obtain ⟨cy, hcy, -⟩ := d₁ y₁ ty₁
  have T1 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G a.A m.φ a.φ g D.g u a.u Hm a.Hm χ a.χ D.t.PP.isLB
    hab hp a.cart d₁ d₂ hAH a.ah y₁ x₁ wA vA cy cx c' c ty₁ tx₁ (hwA.trans ly₁.symm) (hvA.trans lx₁.symm) hcy hcx
    hdiff' hdiff
  have T2 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G A' m.φ φ' g g' u u' Hm Hm' χ χ' D.t.PP.isLB
    hab hp hpz d₁ d₂ hAH hah' y₁ x₁ q p cy cx b' a' ty₁ tx₁ (eq'.trans ly₁.symm) (ep.trans lx₁.symm) hcy hcx dq dp
  have hH : a.herm c' c = hermForm Hm' b' a' := T1.trans T2.symm
  rw [hH]
  exact hval

end GlobalTheory.CompanionTheory.Ar.Sl.FrameGram
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.theta_function_archimedean_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), Nonempty (D.Frame σ) ∧ ∀ a : D.Frame σ, (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃! θ, a.IsFn s θ) ∧ (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n) θ, a.IsFn s θ → a.IsTheta n θ) ∧ ∀ x : D.B.carrier, (∃! c, D.IsVec a x c) ∧ ∀ c, D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re ∧ (x ≠ 0 → c ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.frames_main | exact GlobalTheory.CompanionTheory.Ar.Sl.frames_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.frames_main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_inner_product_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (a : 𝓞 E) (c : ℂ), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → IsTanAt t.G z v → IsTanAt t.G z w → (HodgeIP t.G t.PP.L z (v ≫ t.act.act a) w c ↔ HodgeIP t.G t.PP.L z v (w ≫ t.act.act (H.bar a)) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint | exact GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_cmPoint_locBasis_frames :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (τ : E →+* ℂ) (ℓ : Nat.Primes) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → ∃ (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (X : CMPack Z c FU i hP) (v : Vecs X.y D.p) (w : Vecs X.y D.q), k ≤ X.K ∧ IsLocBasis (𝓞 E) ℓ x ∧ X.IsCMFrame τ hx v w := by
  intro E _ _ _ H D l Xo c g ty FU i Z τ ℓ k hk hty hτ
  obtain ⟨P₀, hP₀⟩ := PeriodNonempty.exists_isPeriod E H (FU.Di i) g ty
    (by rw [(FU.sig i).1, (FU.sig i).2]; exact hty)
  have hsum : D.p + D.q = (FU.Di i).p + (FU.Di i).q := by rw [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨P, hP, x, hloc, hx⟩ := GlobalTheory.T.pure_period_local_basis_exists E H (FU.Di i) g ty P₀ D.p D.q ℓ hP₀ hty hsum
  obtain ⟨hli, n, hn, hspan⟩ := id hloc
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (dvd_zero _))
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.pure_family_decomposition E H (FU.Di i) g ty P hP D.p D.q x n hx hspan
  obtain ⟨X, hkX⟩ := GlobalTheory.T.exists_cmPack_field_ge_of_isPeriod E H D l Xo c g ty FU i Z P hP n k hk hn0 hsplit
  obtain ⟨⟨v, w, hvw⟩, -⟩ := GlobalTheory.T.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hli
  exact ⟨P, hP, x, hx, X, v, w, hkX, hloc, hvw⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_pack_product_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (V : Subring X.K) [IsLocalRing V], 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ s : 𝓞 X.K, (s : X.K) ∈ V) → IsUnit (N : V) → ∃ (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (uV : Fin g → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G _ (uV k)) ∧ (∀ w, IsTanAt T.G _ w → ∃! cc : Fin g → V, IsComb cc uV w) ∧ ∀ k u, X.IsImage (b k) (a k) u → ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = u.left ∧ s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame | exact GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame | (intros; apply GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.cusp_volume_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, U w' = U w) ∧ ∀ m, ∀ t ∈ Q.V m, U (Q.γ m t) = ((Q.F (Q.pc m)).R t).cuspW (Q.F (Q.pc m)).σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets | exact GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.pair_sum_frame_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), HodgeMetric.PolarisedAt 𝔐.t z → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∃ Γ : Matrix (Fin N) (Fin N) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) Γ ∧ Γ.PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.gram_matrix_two_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b b' : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) Ω) (Tz : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ' → (∀ q, b' q = ∑ p, T p q • b p) → (∀ p q, ValAt 𝔐.ξ z (T p q) (Tz p q)) → Γ' = Tz.conjTranspose * Γ * Tz := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change <;> assumption)
end
