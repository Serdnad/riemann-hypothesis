module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle661
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle662
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExact
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Properties
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.exists_continuousOn_frameDirections_inverse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ e.source) → ∃ (W : V → Matrix (Letter Dw) (Fin g) ℂ) (Wi : V → Matrix (Fin g) (Letter Dw) ℂ), ContinuousOn W B ∧ ContinuousOn Wi B ∧ ∀ b ∈ B, Dirs (a b) (fun w => (ex (a b).1 w).left) (W b) ∧ W b * Wi b = 1 ∧ Wi b * W b = 1 := by
  first | exact @GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn | exact GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn | (intros; apply GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.horizontalCoordinate_polynomial_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (g r : ℕ) (T₀ : Di.La ≃+ (Fin r → ℤ)) (ρ : Fin g → Fin r → ℂ), IsPerBasis Di x hm → ∃ (C : ℝ) (k : ℕ), ∀ (Q : Di.La →+ (Letter Dw → ℂ)) (W : Matrix (Letter Dw) (Fin g) ℂ) (Wi : Matrix (Fin g) (Letter Dw) ℂ) (lam : Fin r → Fin g → ℂ) (A : ℝ), GoodPer c σ τ x hm Q → W * Wi = 1 → Wi * W = 1 → (∀ v, ∑ z, Q v z • W z = ∑ m, T₀ v m • lam m) → (∀ j, ∑ m, ρ j m • lam m = Pi.single j 1) → 1 ≤ A → (∀ z j, ‖W z j‖ ≤ A) → (∀ j z, ‖Wi j z‖ ≤ A) → (∀ m j, ‖lam m j‖ ≤ A) → ‖perVal c σ τ x hm Q‖ ≤ C * A ^ k ∧ ‖(perVal c σ τ x hm Q)⁻¹‖ ≤ C * A ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.PolyBd.perVal_bound | exact GlobalTheory.ShFam.Hor.PolyBd.perVal_bound | (intros; apply GlobalTheory.ShFam.Hor.PolyBd.perVal_bound <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.periods_change_of_eigenFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  first | exact @GlobalTheory.ShFam.Hor.per_chg | exact GlobalTheory.ShFam.Hor.per_chg | (intros; apply GlobalTheory.ShFam.Hor.per_chg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.exists_locally_holomorphic_periods_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → ∀ b₀ ∈ B, ∃ (B' : Set V) (i : Fin Fu.n) (Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', Per Fu (a b) i (Q b)) ∧ ∀ v z, DifferentiableOn ℂ (fun b => Q b v z) B' := by
  first | exact @GlobalTheory.ShFam.HorLift.exists_hol_per | exact GlobalTheory.ShFam.HorLift.exists_hol_per | (intros; apply GlobalTheory.ShFam.HorLift.exists_hol_per <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Set GlobalTheory.CxPts GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.ShFam.Hor.Sec

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d}
  {A : Set (CxPts p σ)}

theorem eqOn_of_dense (hA : Dense A) {T : Set (CxPts p σ)} (hT : IsOpen T) {f g : CxPts p σ → ℂ}
    (hf : R.HoloOn T f) (hg : R.HoloOn T g) (h : EqOn f g (T ∩ A)) : EqOn f g T :=
  h.of_subset_closure (hf.continuousOn hT) (hg.continuousOn hT) inter_subset_left (hA.open_subset_closure_inter hT)

theorem exists_holoOn_of_local (hA : Dense A) {S : Set (CxPts p σ)} {u : CxPts p σ → ℂ}
    (h : ∀ y ∈ S, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn S f ∧ EqOn f u (S ∩ A) := by
  choose! T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := fun y : S => T y) (fun y => hT y y.2)
    (fun y hS => ⟨⟨y, hS⟩, hy y hS⟩) fun y => ((hf y y.2).mono inter_subset_right).congr fun z hz => ?_,
    fun y hS => he y hS.1 ⟨hy y hS.1, hS.2⟩⟩
  exact eqOn_of_dense hA ((hT z hz.1).inter (hT y y.2)) ((hf z hz.1).mono inter_subset_left)
    ((hf y y.2).mono inter_subset_right)
    (fun w hw => (he z hz.1 ⟨hw.1.1, hw.2⟩).trans (he y y.2 ⟨hw.1.2, hw.2⟩).symm) ⟨hy z hz.1, hz.2⟩

theorem isHolTo_symm (c : AlgChart p σ d) {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB : IsOpen B) (h : B ⊆ c.e.target) :
    IsHolTo B fun b => (c.e.symm b).1 := fun U f => by
  refine ⟨?_, (c.holo U f).mono fun b hb => ⟨h hb.1, hb.2⟩⟩
  exact (c.e.continuousOn_symm.mono h).isOpen_inter_preimage hB (isOpen_ptsIn U)

variable [IsIntegral Y]

theorem ev_mul_eq {U V W : Y.Opens} {a : Γ(Y, U)} {b : Γ(Y, V)} {c : Γ(Y, W)} {y : CxPts p σ}
    (hU : y ∈ ptsIn p σ U) (hV : y ∈ ptsIn p σ V) (hW : y ∈ ptsIn p σ W)
    (h : ∀ h₁ h₂ h₃, fnOf U h₁ a * fnOf V h₂ b = fnOf W h₃ c) : ev p σ U a y * ev p σ V b y = ev p σ W c y := by
  have hy : y ∈ ptsIn p σ (U ⊓ V ⊓ W) := mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hU, hV⟩, hW⟩
  rw [← ev_res (inf_le_left.trans inf_le_left) hy, ← ev_res (inf_le_left.trans inf_le_right) hy,
    ← ev_res inf_le_right hy, ← ev_mul]
  congr 1
  exact fn_ext fun _ => by rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, h]

theorem holSec_ne_bot [Nonempty (CxPts p σ)] (hA : Dense A) (D : CartierDiv Y) (W : Y → Y.Opens)
    (δ : Y → Y.functionFieldˣ) (hW : ∀ y, y ∈ W y) (hδ : ∀ y, ∀ y' ∈ W y, D.IsEqn y' (δ y))
    (u : Y → CxPts p σ → ℂ) (hu : ∀ y, R.HoloOn (ptsIn p σ (W y)) (u y))
    (h0 : ∀ y, ∀ z ∈ ptsIn p σ (W y) ∩ A, u y z ≠ 0)
    (hc : ∀ y y' (r : Γ(Y, W y ⊓ W y')), (∀ h, fnOf _ h r = (δ y : Y.functionField) / (δ y' : Y.functionField)) →
      ∀ z ∈ ptsIn p σ (W y ⊓ W y') ∩ A, u y z = ev p σ _ r z * u y' z) :
    R.holSec (toLB D) ≠ ⊥ := by
  choose r hr using fun (i : (toLB D).ι) (y : Y) => exists_unit_fnOf_eq (U := (toLB D).U i ⊓ W y)
    (f := (i.1.2 : Y.functionField) / (δ y : Y.functionField))
    fun x hx => (hδ y x hx.2).iff_unitAt.1 (i.2.2 x hx.1)
  let pt (z : CxPts p σ) : Y := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : CxPts p σ) : z ∈ ptsIn p σ (W (pt z)) := mem_ptsIn.2 (hW _)
  let s (i : (toLB D).ι) (z : CxPts p σ) : ℂ := ev p σ _ (r i (pt z)).val z * u (pt z) z
  have key {i y z} (hi : z ∈ ptsIn p σ ((toLB D).U i)) (hy : z ∈ ptsIn p σ (W y)) :
      s i z = ev p σ _ (r i y).val z * u y z := by
    obtain ⟨t, ht⟩ := exists_unit_fnOf_eq (U := W (pt z) ⊓ W y)
      (f := (δ (pt z) : Y.functionField) / (δ y : Y.functionField))
      fun x hx => (hδ y x hx.2).iff_unitAt.1 (hδ _ x hx.1)
    have hz := mem_ptsIn_inf.2 ⟨hpt z, hy⟩
    have e : u (pt z) z = ev p σ _ t.val z * u y z :=
      eqOn_of_dense (R := R) hA (isOpen_ptsIn _) ((hu _).mono (ptsIn_mono inf_le_left))
        ((R.holoOn_ev _ t.val).mul ((hu y).mono (ptsIn_mono inf_le_right))) (hc _ _ _ ht) hz
    rw [← ev_mul_eq (a := (r i (pt z)).val) (b := t.val) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩) hz (mem_ptsIn_inf.2 ⟨hi, hy⟩)
      fun _ _ _ => by rw [hr, hr, ht, div_mul_div_cancel₀ (Units.ne_zero _)], _root_.mul_assoc, ← e]
  have hs : s ∈ R.holSec (toLB D) := by
    refine ⟨⟨fun i j z hi hj => ?_, fun i z hi => ?_⟩, fun i => ?_⟩
    · have e := ev_mul_eq (a := ((toLB D).g i j).val) (b := (r j (pt z)).val) (c := (r i (pt z)).val)
        (mem_ptsIn_inf.2 ⟨hi, hj⟩) (mem_ptsIn_inf.2 ⟨hj, hpt z⟩) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩)
        fun _ _ _ => by rw [hr, hr, fnOf_toLB_g, div_mul_div_cancel₀ (Units.ne_zero _)]
      simp only [s]
      rw [← e, _root_.mul_assoc]
      rfl
    · simp only [s]
      rw [ev_of_notMem (fun h => hi (mem_ptsIn_inf.1 h).1), zero_mul]
    · exact AnRead.holoOn_of_cover (T := fun y => ptsIn p σ (W y)) (fun y => isOpen_ptsIn _)
        (fun z _ => ⟨_, hpt z⟩) fun y =>
        ((AnRead.holoOn_ev_of_subset (r i y).val fun _ => mem_ptsIn_inf.2).mul
          ((hu y).mono inter_subset_right)).congr fun z hz => key hz.1 hz.2
  obtain ⟨z, hz⟩ := hA.nonempty
  intro hb
  rw [hb, Submodule.mem_bot] at hs
  let i : (toLB D).ι := ⟨(W (pt z), δ (pt z)), gen_mem (hW _), hδ _⟩
  exact mul_ne_zero (ev_ne_zero (mem_ptsIn_inf.2 ⟨hpt z, hpt z⟩) (r i (pt z)).isUnit) (h0 _ z ⟨hpt z, hz⟩)
    (congrFun (congrFun hs i) z)

end General

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem logGrowth_inv {h : CxFr Z σ → ℂ} (hg : LogGrowth h) : LogGrowth fun a => (h a)⁻¹ := fun x₀ => by
  obtain ⟨N, φ, h₁, h₂, h₃, h₄, h₅⟩ := hg x₀
  refine ⟨N, φ, h₁, h₂, h₃, h₄, fun V _ _ _ B a hB ha hN b₀ hb => ?_⟩
  obtain ⟨C, k, hk⟩ := h₅ V B a hB ha hN b₀ hb
  exact ⟨C, k, hk.mono fun b hb hi => ⟨(hb hi).2, by rw [inv_inv]; exact (hb hi).1⟩⟩

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ' : k →+* ℂ} {d : ℕ}

theorem inner_iff {π : Y ⟶ gen Z} {z : CxPts p σ'} {x : CxPts (genStr Z) σ} (h : x.1 = z.1 ≫ π) :
    Inner x ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) := by
  rw [Inner, h, mem_ptsIn]
  rfl

theorem exists_extension (R : AnRead p σ' d) (π : Y ⟶ gen Z)
    (hA : Dense (ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl))) {S : Set (CxPts p σ')} (hS : IsOpen S)
    {a : CxPts p σ' → CxFr Z σ} (ha : ∀ z ∈ S, (a z).1.1 = z.1 ≫ π)
    (hf : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (x : V → CxPts p σ'), IsOpen B → IsHolTo B (fun b => (x b).1) → MapsTo x B S → HolFam B fun b => a (x b))
    {h : CxFr Z σ → ℂ}
    (hh : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → DifferentiableOn ℂ (fun b => h (a b)) B)
    (hg : LogGrowth h) :
    ∃ f, R.HoloOn S f ∧ EqOn f (fun z => h (a z)) (S ∩ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl)) := by
  refine exists_holoOn_of_local hA fun y hy => ?_
  obtain ⟨N, φ, hN, hyN, hφ, hφ0, hgr⟩ := hg (a y).1
  obtain ⟨N', hN', rfl⟩ := isOpen_induced_iff.1 hN
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  let T : Set (CxPts p σ') := S ∩ (fun z => z.1 ≫ π) ⁻¹' N'
  have hT : IsOpen T := hS.inter (hN'.preimage ((Points.continuous_comp π).comp continuous_subtype_val))
  have hTN (z) (hz : z ∈ T) : (a z).1 ∈ Subtype.val ⁻¹' N' := by
    rw [mem_preimage, ha z hz.1]; exact hz.2
  have hyT : y ∈ T := ⟨hy, by rw [mem_preimage, ← ha y hy]; exact hyN⟩
  let B := c.e.target ∩ c.e.symm ⁻¹' T
  have hB : IsOpen B := ChartGlue.isOpen_over c.e hT
  have hfam {B' : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB' : IsOpen B') (e : B' ⊆ B) : HolFam B' fun b => a (c.e.symm b) :=
    hf _ B' c.e.symm hB' (isHolTo_symm c hB' (e.trans inter_subset_left)) fun b hb => (e hb).2.1
  have hφB : DifferentiableOn ℂ (fun b => φ (a (c.e.symm b)).1) B :=
    hφ _ B (fun b => (a (c.e.symm b)).1) hB (hfam hB subset_rfl).1 fun b hb => hTN _ hb.2
  have hin (z) (hz : z ∈ T) : φ (a z).1 ≠ 0 ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) :=
    (hφ0 _ (hTN z hz)).trans (inner_iff (ha z hz.1))
  have hB' : IsOpen {b ∈ B | φ (a (c.e.symm b)).1 ≠ 0} :=
    hφB.continuousOn.isOpen_inter_preimage hB isOpen_ne
  obtain ⟨u, hu, he⟩ := GlobalTheory.T.riemann_extension_of_log_growth _ B _ (fun b => h (a (c.e.symm b))) hB hφB
    (hh _ _ _ hB' (hfam hB' (sep_subset _ _)) fun b hb => (hφ0 _ (hTN _ hb.1.2)).1 hb.2)
    (fun b hb => by
      have hs := c.e.map_target hb.1
      have h₁ := hA.open_subset_closure_inter (c.e.open_source.inter hT) ⟨hs, hb.2⟩
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb.1] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, ?_⟩
      rw [c.e.left_inv hz.1.1]
      exact (hin z hz.1.2).2 hz.2)
    fun b hb => by
      obtain ⟨C, n, hn⟩ := hgr _ B _ hB (hfam hB subset_rfl) (fun b hb => hTN _ hb.2) b hb
      refine ⟨C, n, ?_⟩
      filter_upwards [hn, hB.mem_nhds hb] with b' h₁ h₂ h₃
      exact (h₁ ((hφ0 _ (hTN _ h₂.2)).1 h₃)).1
  refine ⟨c.e.source ∩ T, u ∘ c.e, c.e.open_source.inter hT, ⟨hi, hyT⟩,
    AnRead.holoOn_of_chart c (hu.congr fun b hb => congrArg u (c.e.right_inv hb.1)), fun z hz => ?_⟩
  have := he (x := c.e z) ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, by
    rw [c.e.left_inv hz.1.1]; exact (hin z hz.1.2).2 hz.2⟩
  simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this

end Flag

end GlobalTheory.ShFam.Hor.Sec
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (Q : Di.La →+ (Letter Dw → ℂ)) (gm : Di.La ≃ₗ[𝓞 E] Di.La), IsPerBasis Di x hm → GoodPer c σ τ x hm Q → IsIsom Di gm → GoodPer c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) ∧ ‖perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom)‖ = ‖perVal c σ τ x hm Q‖ ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → IsLev l Di gm → perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) = perVal c σ τ x hm Q) := by
  first | exact @GlobalTheory.ShFam.HorIso.perVal_isom | exact GlobalTheory.ShFam.HorIso.perVal_isom | (intros; apply GlobalTheory.ShFam.HorIso.perVal_isom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (a : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (x : Idx Dw τ → (Fu.Di i).La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), Per Fu a i Q → IsPerBasis (Fu.Di i) x hm → GoodPer c σ τ x hm Q := by
  first | exact @GlobalTheory.ShFam.Hor.goodPer_of_per | exact GlobalTheory.ShFam.Hor.goodPer_of_per | (intros; apply GlobalTheory.ShFam.Hor.goodPer_of_per <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem psiCoord_associated {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {χ : D.X} {r r' : R}
    (h : PsiCoord D χ r) (h' : PsiCoord D χ r') : Associated r r' := by
  obtain ⟨x, hx, ex⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 h
  obtain ⟨x', hx', ex'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r').1 h'
  obtain ⟨u, hu⟩ := hx.unique hx'
  have e1 : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u * r') := by
    rw [← ex, hu, map_mul, ← ex']
    rfl
  have e2 : r = u * r' := IsFractionRing.injective R (FractionRing R) e1
  exact ⟨u⁻¹, by rw [e2, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩

end GlobalTheory.TorRef
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem natCard_torsion_quot_span_dvd_of_range_subset :
    ∀ (L : Type) [AddCommGroup L] {m n : ℕ} (δ : Fin m → L) (γ : Fin n → L), LinearIndependent ℤ δ →
    Set.range γ ⊆ Set.range δ →
    Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ))) ∣
      Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))) := by
  intro L _ m n δ γ hli hsub
  have hAB : Submodule.span ℤ (Set.range γ) ≤ Submodule.span ℤ (Set.range δ) :=
    Submodule.span_mono hsub
  have key : ∀ z : L, z ∈ Submodule.span ℤ (Set.range δ) → ∀ a : ℤ, a ≠ 0 →
      a • z ∈ Submodule.span ℤ (Set.range γ) → z ∈ Submodule.span ℤ (Set.range γ) := by
    intro z hz a ha haz
    have himg : δ '' (δ ⁻¹' Set.range γ) = Set.range γ := Set.image_preimage_eq_of_subset hsub
    rw [← himg] at haz ⊢
    rw [Finsupp.mem_span_image_iff_linearCombination] at haz ⊢
    obtain ⟨l', hl'S, hl'⟩ := haz
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
    obtain ⟨c, hc⟩ := hz
    have hlc : Finsupp.linearCombination ℤ δ c = z := by
      rw [Finsupp.linearCombination_apply]; exact hc
    have heq : a • c = l' := by
      apply hli
      rw [map_smul, hlc, hl']
    refine ⟨c, ?_, hlc⟩
    rw [Finsupp.mem_supported'] at hl'S ⊢
    intro i hi
    have := hl'S i hi
    rw [← heq, Finsupp.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  let q : (L ⧸ Submodule.span ℤ (Set.range γ)) →ₗ[ℤ] (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    Submodule.factor hAB
  let f : Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ)) →+
      Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    (q.restrict (p := Submodule.torsion ℤ _) (q := Submodule.torsion ℤ _) (fun x hx => by
      rw [Submodule.mem_torsion_iff] at hx ⊢
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [Submonoid.smul_def] at ha ⊢; rw [← map_smul, ha, map_zero]⟩)).toAddMonoidHom
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ hfx
    have hqx : q x = 0 := congrArg Subtype.val hfx
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.mem_torsion_iff] at hx
      obtain ⟨⟨a, ha0⟩, ha⟩ := hx
      have hz : z ∈ Submodule.span ℤ (Set.range δ) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        simpa [q] using hqx
      have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
      have haz : a • z ∈ Submodule.span ℤ (Set.range γ) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
        simpa [Submonoid.smul_def] using ha
      rw [Submodule.Quotient.mk_eq_zero]
      exact key z hz a ha' haz
  exact AddSubgroup.card_dvd_of_injective f hinj

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BlowOpen

theorem exists_specializes_of_dense {X : Type} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X] (S : Set X)
    (hSo : IsOpen S) (hSd : Dense S) (x : X) : ∃ w ∈ S, w ⤳ x := by
  classical
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_of_mem_irreducibleComponents _ hC
  have hη : IsGenericPoint hCi.genericPoint (irreducibleComponent x) := by
    simpa [hCc.closure_eq] using hCi.isGenericPoint_genericPoint_closure
  let F := ⋃ C' ∈ (irreducibleComponents X \ {irreducibleComponent x}), C'
  have hFc : IsClosed F := (NoetherianSpace.finite_irreducibleComponents.diff).isClosed_biUnion
    (fun C' h => isClosed_of_mem_irreducibleComponents C' h.1)
  have hηF : hCi.genericPoint ∉ F := by
    simp only [F, Set.mem_iUnion]
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hsub : irreducibleComponent x ⊆ C' := fun y hy =>
      (hη.specializes hy).mem_closed (isClosed_of_mem_irreducibleComponents C' hC') hηC'
    exact hne (Set.mem_singleton_iff.2 (hC.eq_of_le hC'.1 hsub).symm)
  obtain ⟨w, hwF, hwS⟩ := hSd.inter_open_nonempty Fᶜ hFc.isOpen_compl ⟨_, hηF⟩
  have hwC : w ∈ irreducibleComponent x := by
    by_contra h
    apply hwF
    simp only [F, Set.mem_iUnion]
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => h ?_⟩,
      mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.1 e]; exact mem_irreducibleComponent
  exact ⟨_, (hη.specializes hwC).mem_open hSo hwS, hη.specializes mem_irreducibleComponent⟩

theorem exists_specializes_of_dense_scheme (N : Scheme.{0}) [IsLocallyNoetherian N] (W : Set N) (hWo : IsOpen W)
    (hWd : Dense W) (n : N) : ∃ w ∈ W, w ⤳ n := by
  obtain ⟨_, ⟨O, hO, rfl⟩, hnO, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ n) isOpen_univ
  haveI : IsNoetherianRing Γ(N, O) := IsLocallyNoetherian.component_noetherian ⟨O, hO⟩
  obtain ⟨w, hw, hwn⟩ := @exists_specializes_of_dense (O : Set N) _ O.isOpen.isOpenEmbedding_subtypeVal.quasiSober
    (noetherianSpace_of_isAffineOpen O hO) (Subtype.val ⁻¹' W : Set (O : Set N)) (hWo.preimage continuous_subtype_val)
    (hWd.preimage O.isOpen.isOpenMap_subtype_val) ⟨n, hnO⟩
  exact ⟨w, hw, hwn.map continuous_subtype_val⟩

end GlobalTheory.BlowOpen
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.LocalRingGeneralisation

theorem stalk_fromSpecStalk_equiv (X : Scheme.{0}) (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))) ≃+*
        Localization.AtPrime p,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈ U)
        (hx : x ∈ U) (s : Γ(X, U)),
        e ((X.presheaf.germ U _ hq).hom s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  rw [← h2]
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

end GlobalTheory.LocalRingGeneralisation
end
