module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordsOverField
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle273
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle124
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle271
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle213
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeBound
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeight
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

alias _root_.GlobalTheory.T.root_origin_coords_over_field :=
  GlobalTheory.CompanionTheory.Ar.root_model_on_cover
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.intersection_system_weight_left : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ U : ((Σ k, J k) → ℂ) → ℝ, Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ w, 0 ≤ U w) ∧ (∀ w (a : K → ℂ), (∀ k, a k ≠ 0) → U (torusSmul a w) = U w) ∧ (∀ w, U (conjVec w) = U w) ∧ ∀ U', Or.𝔐.IsCuspWeight Or.sm U' → ∀ w ∈ Dc.Xo, U' w = U w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx.exists_cuspWeight | exact GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx.exists_cuspWeight | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx.exists_cuspWeight <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

theorem _root_.GlobalTheory.T.hodge_component_holomorphic_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n a : ℕ) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (N : ℕ) (s : Fin N → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), a ≤ n → DifferentiableOn ℂ w (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, w u ∈ mcPts (mCoordIdeal y)) → (∀ u ∈ Flat.punct n a 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w u) → 𝔐.Interior z) → CoordsAt 𝔐.ξ y z₀ (w 0) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (ρ : ℝ) (τ : c.F →+* ℂ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : Fin N → Fin C.g → C.R), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (w ((ρ : ℂ) • u)) ∧ spMap (C.ψ u) ≫ jj ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.exists_chart_at_of_polydisc | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.exists_chart_at_of_polydisc | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.exists_chart_at_of_polydisc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


theorem _root_.GlobalTheory.T.section_module_field_ext_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D'), ∃ P : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) → SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), (∀ (a : 𝓞 L) s, P (a • s) = algebraMap (𝓞 L) (𝓞 L') a • P s) ∧ ∀ (s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (b' : Sp (𝓞 L')) (y : D.t.G.left), D.t.G.hom y = spMap (algebraMap (𝓞 L) (𝓞 L')) b' → y ∈ Out.nonzeroLocus (M := (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) s → ∃ y' : D'.t.G.left, D'.t.G.hom y' = b' ∧ y' ∈ Out.nonzeroLocus (M := (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (P s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

section Segre

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

abbrev segJ (J : K → Type) : K ⊕ Unit → Type := Sum.elim J fun _ : Unit => ∀ k, J k

instance segJ.instFintype : ∀ k, Fintype (segJ J k)
  | .inl k => inferInstanceAs (Fintype (J k))
  | .inr _ => (Fintype.ofFinite (∀ k, J k) : Fintype (∀ k, J k))

def segBlock (y : (Σ k, J k) → Ω) : (Σ _ : Unit, ∀ k, J k) → Ω := fun p => ∏ k, y ⟨k, p.2 k⟩

def segY (y : (Σ k, J k) → Ω) : (Σ k, segJ J k) → Ω
  | ⟨.inl k, i⟩ => y ⟨k, i⟩
  | ⟨.inr _, c⟩ => ∏ k, y ⟨k, c k⟩

theorem segY_prod (y : (Σ k, J k) → Ω) (c : (k : K ⊕ Unit) → segJ J k) :
    ∏ k, segY y ⟨k, c k⟩ = (∏ k, y ⟨k, c (Sum.inl k)⟩) * ∏ k, y ⟨k, c (Sum.inr ()) k⟩ := by
  rw [Fintype.prod_sum_type]
  simp [segY]

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {y : (Σ k, J k) → Ω}

theorem segTie (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) :
    CoordTie ℤ ξ fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩ := by
  have key := @GlobalTheory.T.coords_join_blocks X Ω _ ξ K _ J _ y Unit _ (fun _ => ∀ k, J k) (fun _ => Fintype.ofFinite _) (segBlock y) h
    (fun _ p => by
      obtain ⟨c, hc⟩ := h.cover p
      exact ⟨c, hc⟩)
  have e : (fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩) =
      fun c' : (k : K ⊕ Unit) → Sum.elim J (fun _ : Unit => ∀ k, J k) k =>
        (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, segBlock y ⟨k, c' (Sum.inr k)⟩ := by
    funext c'
    rw [segY_prod]
    simp [segBlock]
  rw [e]
  exact key

theorem segChart {c : (k : K ⊕ Unit) → segJ J k} {p : Cpt ξ}
    (h : InChart ξ (fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩) c p) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (fun k => c (Sum.inl k)) p := by
  obtain ⟨h0, h1⟩ := h
  simp only [segY_prod] at h0 h1
  have hB := right_ne_zero_of_mul h0
  refine ⟨left_ne_zero_of_mul h0, fun c' => ?_⟩
  have h2 := h1 (fun k => match k with
    | .inl k => c' k
    | .inr u => c (Sum.inr u))
  simp only at h2
  rwa [mul_div_mul_right _ _ hB] at h2

theorem segDeg {F : Type} [AddCommGroup F] [Module Ω F] {L : Lat ξ F} {a : K → ℤ} {e₀ : F}
    (h : L.IsDegOn Set.univ y a e₀) : L.IsDegOn Set.univ (segY y) (Sum.elim a 0) e₀ := by
  refine ⟨h.1, fun p _ c' hc => ?_⟩
  have h1 := h.2 p trivial (fun k => c' (Sum.inl k)) (segChart hc)
  have e : (∏ k, segY y ⟨k, c' k⟩ ^ (Sum.elim a 0 : K ⊕ Unit → ℤ) k) =
      ∏ k, y ⟨k, c' (Sum.inl k)⟩ ^ a k := by
    rw [Fintype.prod_sum_type]
    simp [segY]
  rw [e]
  exact h1

end Segre

section Ideal

variable {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
  [∀ k, Fintype (J' k)]

theorem mem_mcPts_map (v : (Σ k, J k) → Σ k, J' k) (bd : Ideal (MRing J)) (w : (Σ k, J' k) → ℂ)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hw' : ∀ k, ∃ i, w (v ⟨k, i⟩) ≠ 0) :
    w ∈ mcPts (bd.map (MvPolynomial.rename v)) ↔ (fun p => w (v p)) ∈ mcPts bd := by
  have e : ∀ f : MRing J, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ)
      (MvPolynomial.rename v f)) =
      MvPolynomial.eval (fun p => w (v p)) (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro f
    rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
    rfl
  constructor
  · intro h
    exact ⟨hw', fun f hf => by
      rw [← e]
      exact h.2 _ (Ideal.mem_map_of_mem _ hf)⟩
  · intro h
    refine ⟨hw, fun f hf => ?_⟩
    let φ : MRing J' →+* ℂ := (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ))
    have hle : bd.map (MvPolynomial.rename v) ≤ RingHom.ker φ :=
      Ideal.map_le_iff_le_comap.2 fun g hg => by
        show φ (MvPolynomial.rename v g) = 0
        show MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.rename v g)) = 0
        rw [e]
        exact h.2 g hg
    exact hle hf

end Ideal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HodgeCpt.retie {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {K₂ : Type} [Fintype K₂] {J₂ : K₂ → Type} {y₂ : (Σ k, J₂ k) → Ω}
    (h : CoordTie ℤ 𝔐.ξ fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) : HodgeCpt Y S y₂ where
  X := 𝔐.X
  ξ := 𝔐.ξ
  all := 𝔐.all
  tie := h
  normal := 𝔐.normal
  f := 𝔐.f
  Ω₀ := 𝔐.Ω₀
  ξ₀ := 𝔐.ξ₀
  gen₀ := 𝔐.gen₀
  cst := 𝔐.cst
  cst_over := 𝔐.cst_over
  fn := 𝔐.fn
  fn_over := 𝔐.fn_over
  t := 𝔐.t
  m := 𝔐.m
  Li := 𝔐.Li
  M := 𝔐.M
  ρ := 𝔐.ρ
  act := 𝔐.act
  S_prime := 𝔐.S_prime
  R := 𝔐.R
  R_ge := 𝔐.R_ge
  tors := 𝔐.tors
  vb := 𝔐.vb

def HodgeCpt.Flag.retie {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) {K₂ : Type} [Fintype K₂] {J₂ : K₂ → Type}
    {y₂ : (Σ k, J₂ k) → Ω} (h : CoordTie ℤ 𝔐.ξ fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) :
    (𝔐.retie h).Flag where
  b := Fl.b
  sub := Fl.sub
  Li₀ := Fl.Li₀
  acg := Fl.acg
  mod := Fl.mod
  M₀ := Fl.M₀
  j := Fl.j
  j_pt := Fl.j_pt
  V₀ := Fl.V₀
  V₀_mem := Fl.V₀_mem
  deg := Fl.deg
  generic := Fl.generic

end GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_refGeo : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ G : RefGeo Y, genPt G.𝔐.ξ₀ = genPt ξ₀ := by
  intro hRes E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hgen
  haveI : CharZero Ω₀ := GlobalTheory.T.component_generic_char_zero E H D l Xo c Y Ω₀ ξ₀ hgen
  obtain ⟨K₀, _, J₀, _, y₀, X₀, ξ', f₀, cst₀, t₀, m₀, Li', _, _, M', ρ', L', bd₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ :=
    GlobalTheory.T.exists_coords_for_component hRes E H D l Xo c Y Ω₀ ξ₀ hgen
  obtain ⟨Ω, _, _, _, K, _, J, _, y, X, ξ, f, cst, t, m, Li, _, _, M, ρ, Li₀, _, _, M₀, j, V₀, b, bd,
    hall, htie, hnorm, hdom, hcst, hact, hjpt, hV, hflag, hvb, hsnc, hbd⟩ :=
    GlobalTheory.T.coords_with_constants_map E H D l Xo c Y Ω₀ ξ₀ K₀ J₀ y₀ X₀ ξ' f₀ cst₀ t₀ m₀ Li' M' ρ' L' bd₀ hgen h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  obtain ⟨K', _, J', _, y', bk, bx, 𝔐, g, Fl, xdeg, e, hbk, hy, hξ, hf, hg0, hdeg, hlines, -, hreg, hinj⟩ :=
    GlobalTheory.T.generic_coords_descend_subfield E H D l Xo c Y Ω K J y X ξ f Ω₀ ξ₀ cst t m Li M ρ Li₀ M₀ j V₀ b 1 hall htie hnorm hgen hdom hcst
      hact hjpt hV hflag hvb
  have tie₂ := segTie (y := y') 𝔐.tie
  have hy₂ : ∀ k (a : J k), segY y' ⟨Sum.inl (bk k), bx k a⟩ = y ⟨k, a⟩ := hy
  let v : (Σ k, J k) → Σ k, segJ J' k := fun p => ⟨Sum.inl (bk p.1), bx p.1 p.2⟩
  refine ⟨{ Ω := Ω, K := K' ⊕ Unit, J := segJ J', y := segY y', 𝔐 := 𝔐.retie tie₂, Fl := Fl.retie tie₂,
            deg_one := hdeg, xdeg := fun r => Sum.elim (xdeg r) 0, e := e, lines := ?_,
            bd := bd.map (MvPolynomial.rename v), snc := ?_, bd_iff := ?_, k₀ := Sum.inr (), embeds := ?_ }, hg0⟩
  · exact fun r => segDeg (hlines r)
  · have hfin : (GlobalTheory.CompHt.fintypePsi : Fintype (CMType H)) = Subtype.fintype _ :=
      Subsingleton.elim _ _
    rw [hfin] at hsnc
    exact GlobalTheory.T.snc_model_reindexed_coords X 𝔐.X Ω ξ 𝔐.ξ g K J y (K' ⊕ Unit) (segJ J') (segY y') (fun k => Sum.inl (bk k)) bx _ bd
      hall 𝔐.all htie tie₂ hξ hy₂ hreg hinj hsnc
  · intro z w hw
    have hw₁ := GlobalTheory.T.complex_coords_reindexed X 𝔐.X Ω ξ 𝔐.ξ g K J y (K' ⊕ Unit) (segJ J') (segY y') (fun k => Sum.inl (bk k)) bx z w
      hall 𝔐.all 𝔐.tie.gen hξ hy₂ hreg hw
    have hne : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
    have hne' : ∀ k, ∃ i, w (v ⟨k, i⟩) ≠ 0 := fun k => (hw₁.1 k).imp fun _ h => h.ne_zero
    rw [mem_mcPts_map v bd w hne hne']
    refine (show (fun p => w (v p)) ∈ mcPts bd ↔ _ from hbd (z ≫ g) _ hw₁).trans ?_
    have hab := abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre z)
    have hc : f (centre (z ≫ g)) = 𝔐.f (centre z) := by
      rw [hf]
      rfl
    rw [hc]
    exact not_congr hab
  · exact GlobalTheory.T.embeds_generic_of_char_zero 𝔐.X Ω 𝔐.ξ _ _ 𝔐.tie

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.intersection_system_hodge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (s : Fin (Dc.N - Dc.j) → Or.𝔐.Li) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Submodule.span Ω (Set.range (b ∘ headIdx Dc.j_le_N)) = Hd.F τ → (∀ k, s k ∈ Or.𝔐.Vgen (Or.sm τ)) → (∀ k, Or.i τ (b (tailIdx Dc.j_le_N k)) - s k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩) → (Or.𝔐.V (Or.sm τ)).IsFrameAt s ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → G.PosDef → ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z s Γ ∧ Γ.PosDef ∧ quotNormSq Dc.j_le_N G = Γ.det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det | exact GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det | (intros; apply GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.frame_function_cm_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (ℓ : Nat.Primes), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → ∃ t : E, (∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ + Real.log ‖j (IsCMField.complexConj E t)‖ + Real.log ‖j (gramE (FU.Di i) e).det‖ = -((D.p : ℝ) + D.q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧ (IsLocBasis (𝓞 E) ℓ e → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ = 0) ∧ ∀ (j : k →+* ℂ_[ℓ]) (t₀ : ℝ), HasFinNorm U τ φ ℓ (j.comp (IntermediateField.inclusion hc).toRingHom) t₀ → t₀ = Real.log ‖j r‖ - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) t)‖ - D.q * logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((D.q : ℝ) - D.p) * (logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (H.rt : E))‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm | exact GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.flatGen_finNorm <;> assumption)
end
