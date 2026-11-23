module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle050
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_fibreSection_nowhereZero_of_pullbackTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : t'.PP.L.Sec), (∀ y : Sp S, ∃ q : t'.G.left, t'.G.hom q = y ∧ q ∈ Out.nonzeroLocus th) → ∃ s : LB.Sec (PPx x), SecNZ x s := by
  first | exact @GlobalTheory.SecTransport.exists_sec_nonzero | exact GlobalTheory.SecTransport.exists_sec_nonzero | (intros; apply GlobalTheory.SecTransport.exists_sec_nonzero <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.FrameGenerator

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem scal_eq_constFn {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) :
    scal x a i = constFn (fst (Over.mk x) Xo.univ.t.G).left _ a := rfl

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  rw [scal_eq_constFn]
  exact (congrArg _ (map_one _)).trans (map_one _)

theorem isPullback_gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) :
    IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
  (IsPullback.of_hasPullback _ _).flip

theorem secGen_of_secNZ (hS : Out.SecBaseChangeSt) {T : Type} [CommRing T] (x : Sp T ⟶ Xo.X)
    (θ : LB.Sec (PPx x)) (h : SecNZ x θ) : SecGen x θ := by
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  intro s
  have hw : LBIso (PPx x) (Xo.univ.t.PP.L.pull (snd (Over.mk x) Xo.univ.t.G).left) :=
    exists_iso_linComb Xo.univ.t.PP.isLB _ _ fun _ _ _ => by simp
  refine SectionBaseChange.generates hS (Obj.toPolAV Xo.univ) (isPullback_gx x)
    (DVR.linComb_isLB _ Xo.univ.t.PP.isLB _ _) hw θ (fun y => ?_) s
  obtain ⟨q, i, hq, hi⟩ := h y
  exact ⟨q, hq, TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩⟩

theorem secNZ_of_secBC {R T : Type} [CommRing R] [CommRing T] {ψ : R →+* T} {j : Sp R ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    {θ : LB.Sec (PPx j)} {θ' : LB.Sec (PPx x')} (h : SecNZ j θ) (hx : x' = spMap ψ ≫ j)
    (hb : SecBC ψ 1 j x' θ θ') : SecNZ x' θ' := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := hb
  have sq : IsPullback pm (fst (Over.mk x') Xo.univ.t.G).left (fst (Over.mk j) Xo.univ.t.G).left (spMap ψ) :=
    IsPullback.of_right (by rw [h₁, ← hx]; exact isPullback_gx x') h₂ (isPullback_gx j)
  intro p
  obtain ⟨q, i, hq, hi⟩ := h (spMap ψ p)
  obtain ⟨q', rfl, e₂⟩ := Scheme.exists_preimage_of_isPullback sq q p hq
  have le : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx j).U i := fun y hy => Set.mem_iInter.2 fun k => by
    have : (snd (Over.mk x') Xo.univ.t.G).left y ∈ Xo.univ.t.PP.L.U (i k) := Set.mem_iInter.1 hy k
    rw [← h₁] at this; exact this
  have mem : q' ∈ (PPx x').U i := Set.mem_iInter.2 fun k => by
    have : (snd (Over.mk j) Xo.univ.t.G).left (pm q') ∈ Xo.univ.t.PP.L.U (i k) :=
      Set.mem_iInter.1 ((Gx j).basicOpen_le _ hi) k
    show (snd (Over.mk x') Xo.univ.t.G).left q' ∈ Xo.univ.t.PP.L.U (i k)
    rw [← h₁]; exact this
  refine ⟨q', i, e₂, ?_⟩
  rw [← h₃ i le, scal_one', _root_.one_mul, Scheme.basicOpen_appLE]
  exact ⟨mem, hi⟩

theorem secGen_of_secNZ_baseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsNoetherianRing R] (j : Sp R ⟶ Xo.X) (θ : LB.Sec (PPx j)), SecNZ j θ → ∀ (T : Type) [CommRing T] (ψ : R →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ j → SecBC ψ 1 j x' θ θ' → SecGen x' θ' :=
  fun hS _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ x' θ' hx hb => secGen_of_secNZ hS x' θ' (secNZ_of_secBC h hx hb)

end GlobalTheory.FrameGenerator
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem exists_sec_generator_fibre (hT : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    {K : Type} [Field K] (y : Sp K ⟶ S) :
    ∃ β : (o.t.PP.L.pull (pullback.fst o.t.G.hom y)).Sec, ∀ s : (o.t.PP.L.pull (pullback.fst o.t.G.hom y)).Sec,
      ∃ a : K, ∀ i, s.f i = constFn (pullback.snd o.t.G.hom y) _ a * β.f i := by
  have h := isGrpPullback_pullback o.t.G y
  obtain ⟨hL, hr, -, hs⟩ := Out.CubePf.cubePull _ _ o.t.G _ (cubeMapOf h) o.t.PP o.t.cub
  have := o.t.semi.smooth
  have : Smooth ((Over.pullback y).obj o.t.G).hom := by
    change Smooth (pullback.snd o.t.G.hom y)
    infer_instance
  obtain ⟨am, kt⟩ := amplePt _ _ y _ _ _ h _ _ o.t.PP.isLB hL ⟨_, Out.CubePf.idIsoL_isGen hL⟩ o.ample o.ktriv
  have := o.t.semi.geomConnected
  have : GeometricallyConnected ((Over.pullback y).obj o.t.G).hom := by
    change GeometricallyConnected (pullback.snd o.t.G.hom y)
    infer_instance
  have : ConnectedSpace ((Over.pullback y).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := ((Over.pullback y).obj o.t.G).hom) (𝟙 _) (𝟙 _)
      ((Over.pullback y).obj o.t.G).hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback y).obj o.t.G).hom
    (eSec ((Over.pullback y).obj o.t.G) (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := hs o.t.sym
  obtain ⟨β, hβ⟩ := principalPolarisation_exists_unique_section hT
    { A := (Over.pullback y).obj o.t.G, g := d, smoothDim := hd, L := ((cubeMapOf h).rigLB o.t.PP hL hr).L
      isLB := hL, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) h.1 o.proper, ‹_›⟩
      rigid := ⟨((cubeMapOf h).rigLB o.t.PP hL hr).rig, ((cubeMapOf h).rigLB o.t.PP hL hr).rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  exact ⟨β, fun s => (hβ s).exists⟩

theorem FamilyUnif_isOpen_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n)
    (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) (V : Xo.univ.t.G.left.Opens) :
    IsOpen {z | ⊤ ≤ (U.ex i P z).left ⁻¹ᵁ V} := by
  have h := ((U.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1
  have c : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  convert h.preimage c using 1
  ext z
  simp

theorem thetaFrame_ratio : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = θ b z * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ h₀ : Matrix (Fin g) (Fin g) ℂ, θ b ≠ 0 → θ b' ≠ 0 → IsUnit h₀.det → (U.u i (P b)) = (U.u i (P b')) → (∀ z, (U.ex i (P b') (h₀ *ᵥ z)).left = (U.ex i (P b) z).left) → ∃ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ρ 0 = 1 ∧ κ ≠ 0 ∧ (∀ z, θ b' (h₀ *ᵥ z) * ρ z = κ * θ b z) ∧ ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b', h₀ *ᵥ z) = ρ z * fr j (b, z) := by
  intro hT E _ _ _ H D l Xo σ g ty U i m B P θ fr hP hd hn hc h0 hs b hb b' hb' h₀ hθ hθ' hdet hu hex
  have cover : ∀ z, ∃ j, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((U.ex i (P b) z).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using cover
  have tr : ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (U.ex i (P b') (h₀ *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z h => by rw [hex]; exact h
  have key : ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b', h₀ *ᵥ z) = fr (J z) (b', h₀ *ᵥ z) / fr (J z) (b, z) * fr j (b, z) := fun j z h => by
    have h1 : ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (J z)) :=
      (top_le_preimage_inf _ _ _).2 ⟨h, hJ z⟩
    have e1 := hc j (J z) b z hb h1
    have e2 := hc j (J z) b' (h₀ *ᵥ z) hb' (by rw [hex]; exact h1)
    rw [hex] at e2
    have := hn _ _ _ hb (hJ z)
    rw [e1, e2]
    field_simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin g → ℂ) → ℂ, ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b', h₀ *ᵥ z) = ρ z * fr j (b, z) := ⟨_, key⟩
  clear key
  have hρ0 : ∀ z, ρ z ≠ 0 := fun z h => hn _ _ _ hb' (tr _ _ (hJ z)) (by rw [hρ _ _ (hJ z), h, zero_mul])

  obtain ⟨s, hs1⟩ := hs b hb
  obtain ⟨s', hs2⟩ := hs b' hb'
  have hs3 : ∃ s' : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec,
      ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b') z).left →
      x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b') z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j))
        (s'.f (fun _ => j)) = θ b' z * fr j (b', z) := by
    rw [hu]; exact ⟨s', hs2⟩
  clear s' hs2
  obtain ⟨s', hs2⟩ := hs3
  obtain ⟨β, hβ⟩ := exists_sec_generator_fibre hT Xo.univ (U.u i (P b))
  obtain ⟨a, ha⟩ := hβ s
  obtain ⟨a', ha'⟩ := hβ s'
  have val : ∀ z, ∃ v : ℂ, a * v = θ b z * fr (J z) (b, z) ∧
      a' * v = θ b' (h₀ *ᵥ z) * (ρ z * fr (J z) (b, z)) := fun z => by
    have w : (U.ex i (P b) z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ U.u i (P b) :=
      (Over.w (U.ex i (P b) z)).trans (Category.id_comp _).symm
    let x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b)) := pullback.lift _ _ w
    have x1 : x ≫ pullback.fst _ _ = (U.ex i (P b) z).left := pullback.lift_fst _ _ _
    have x2 : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hx : ⊤ ≤ x ⁻¹ᵁ (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => J z) := by
      rw [top_le_preimage_iff_mem, mem_pull]
      have := hJ z
      rw [← x1, top_le_preimage_iff_mem] at this
      exact this
    have e1 := hs1 (J z) z x x1 x2 (hJ z)
    have e2 := hs2 (J z) (h₀ *ᵥ z) x (x1.trans (hex z).symm) x2 (tr _ _ (hJ z))
    rw [hρ _ _ (hJ z)] at e2
    have f1 := (congrArg (valAt' x _) (ha (fun _ => J z))).trans ((valAt'_mul _ _ _ _).trans
      (congrArg (· * _) (valAt'_constFn x _ x2 _ _ hx)))
    have f2 := (congrArg (valAt' x _) (ha' (fun _ => J z))).trans ((valAt'_mul _ _ _ _).trans
      (congrArg (· * _) (valAt'_constFn x _ x2 _ _ hx)))
    exact ⟨_, f1.symm.trans e1, f2.symm.trans e2⟩
  have ha0 : a ≠ 0 := fun h => hθ (funext fun z => by
    obtain ⟨v, e, -⟩ := val z
    rw [h, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (hn _ _ _ hb (hJ z)))
  have ha0' : a' ≠ 0 := fun h => hθ' (funext fun w => by
    obtain ⟨v, -, e⟩ := val (h₀⁻¹ *ᵥ w)
    rw [h, zero_mul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (mul_ne_zero (hρ0 _) (hn _ _ _ hb (hJ _))))
  refine ⟨ρ, a' / a, fun z => ?_, hρ0, ?_, div_ne_zero ha0' ha0, fun z => ?_, hρ⟩
  · have ho := FamilyUnif_isOpen_ex U i (P b) (hP b hb) (Xo.univ.t.PP.L.U (J z))
    have hz := ho.mem_nhds (hJ z)
    have d1 : DifferentiableOn ℂ (fun z' => fr (J z) (b, z'))
        {z' | ⊤ ≤ (U.ex i (P b) z').left ⁻¹ᵁ Xo.univ.t.PP.L.U (J z)} :=
      (hd (J z)).comp (f := fun z' => (b, z')) (by fun_prop) (fun z' h => ⟨hb, h⟩)
    have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h₀ *ᵥ z') :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h₀)).differentiable
    have d2 : DifferentiableOn ℂ (fun z' => fr (J z) (b', h₀ *ᵥ z'))
        {z' | ⊤ ≤ (U.ex i (P b) z').left ⁻¹ᵁ Xo.univ.t.PP.L.U (J z)} :=
      (hd (J z)).comp (f := fun z' => (b', h₀ *ᵥ z'))
        ((differentiable_const _).prodMk dl).differentiableOn (fun z' h => ⟨hb', tr _ _ h⟩)
    have d3 := (d2.mul (d1.inv (fun z' h => hn _ _ _ hb h))).congr (f₁ := ρ) (fun z' h => by
      have := hn _ _ _ hb h
      show ρ z' = fr (J z) (b', h₀ *ᵥ z') * (fr (J z) (b, z'))⁻¹
      rw [hρ _ _ h]; field_simp)
    exact d3.differentiableAt hz
  · have e := hρ _ _ (hJ 0)
    have t := tr _ _ (hJ 0)
    rw [Matrix.mulVec_zero] at e t
    have e' : fr (J 0) (b', 0) = fr (J 0) (b, 0) := by rw [h0 _ _ hb (hJ 0), h0 _ _ hb' t, hu]
    rw [e'] at e
    exact ((mul_eq_right₀ (hn _ _ _ hb (hJ 0))).1 e.symm)
  · obtain ⟨v, e1, e2⟩ := val z
    have := hn _ _ _ hb (hJ z)
    apply mul_right_cancel₀ this
    rw [_root_.mul_assoc, ← e2, _root_.mul_assoc, ← e1]
    field_simp

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianSubgroupFinite

theorem exists_lift_of_range_subset {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have hs : Surjective (pullback.snd ν x) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩⟩
  have : IsIso (pullback.snd ν x) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem isCommMonObj_of_mono {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]
    [BraidedCategory 𝒞] {N B : 𝒞} [MonObj N] [MonObj B] [IsCommMonObj B] (ν : N ⟶ B) [Mono ν]
    [IsMonHom ν] : IsCommMonObj N where
  mul_comm := by
    rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]

theorem finite_of_no_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) := by
  intro hcount k _ _ B _ n hB hn hnk C Z hZ hC htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, -, hν₀c, hgc, hg, hfin⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have h1 : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ N₀) // x ^ n = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, one_pow n⟩, fun x => Subtype.ext ?_⟩
    have h2 : x.1 ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, x.2, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  rw [hcount k N₀ g n hA hg hnk] at h1
  have hg0 : g = 0 := by
    rcases (Nat.pow_eq_one.1 h1) with h | h
    · exact absurd h hn.one_lt.ne'
    · omega
  have := hfin hg0
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

end GlobalTheory.AbelianSubgroupFinite
end
