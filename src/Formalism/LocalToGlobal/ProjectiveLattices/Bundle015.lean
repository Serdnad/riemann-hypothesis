module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Unramified.LocalStructure
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj.CompSplitPfD

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology

theorem cspD_gen {X : Type} [TopologicalSpace X] [QuasiSober X] {W : Set X} (hW : W ∈ irreducibleComponents X) :
    IsGenericPoint hW.1.genericPoint W := by
  have h1 := hW.1.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_irreducibleComponents W hW).closure_eq] at h1

theorem cspD_max {X : Type} [TopologicalSpace X] [T0Space X] {W : Set X}
    (hW : W ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η W) (z : X) (hz : z ⤳ η) : z = η := by
  have hWc : closure ({η} : Set X) = W := hη
  have h1 : closure ({η} : Set X) ⊆ closure {z} := specializes_iff_closure_subset.mp hz
  have hirr : IsIrreducible (closure ({z} : Set X)) := isIrreducible_singleton.closure
  have h2 : closure ({z} : Set X) ⊆ W := hW.2 hirr (hWc ▸ h1)
  have h3 : closure ({z} : Set X) = closure {η} := le_antisymm (hWc ▸ h2) h1
  exact (inseparable_iff_closure_eq.mpr h3).eq

theorem cspD_disj {X : Type} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (hloc : ∀ x : X, ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → X), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  rw [Set.disjoint_left]
  intro x hxZ hxZ'
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η Z := ⟨_, cspD_gen hZ⟩
  obtain ⟨η', hη'⟩ : ∃ η', IsGenericPoint η' Z' := ⟨_, cspD_gen hZ'⟩
  have s1 : η ⤳ x := by rw [specializes_iff_mem_closure, hη.def]; exact hxZ
  have s2 : η' ⤳ x := by rw [specializes_iff_mem_closure, hη'.def]; exact hxZ'
  obtain ⟨Y, tY, g, hg, ⟨y, rfl⟩, hY⟩ := hloc x
  have hU : IsOpen (Set.range g) := hg.isOpen_range
  obtain ⟨a, ha⟩ : η ∈ Set.range g := s1.mem_open hU ⟨y, rfl⟩
  obtain ⟨b, hb⟩ : η' ∈ Set.range g := s2.mem_open hU ⟨y, rfl⟩
  have hind := hg.toIsEmbedding.toIsInducing
  have maxa : ∀ a', a' ⤳ a → a' = a := fun a' h => hg.injective (by
    have h' : g a' ⤳ g a := h.map hg.continuous
    rw [ha] at h' ⊢; exact cspD_max hZ hη _ h')
  have maxb : ∀ b', b' ⤳ b → b' = b := fun b' h => hg.injective (by
    have h' : g b' ⤳ g b := h.map hg.continuous
    rw [hb] at h' ⊢; exact cspD_max hZ' hη' _ h')
  have ya : a ⤳ y := hind.specializes_iff.mp (by rw [ha]; exact s1)
  have yb : b ⤳ y := hind.specializes_iff.mp (by rw [hb]; exact s2)
  have hab := hY a b y maxa maxb ya yb
  apply hne
  calc Z = closure {η} := hη.def.symm
    _ = closure {η'} := by rw [← ha, ← hb, hab]
    _ = Z' := hη'.def

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem cspD_smooth (Xo : Moduli Dw l) (c : Coeff l) :
    Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
  first
    | (haveI := Xo.smooth; exact MorphismProperty.pullback_snd _ _ inferInstance)
    | (haveI := Xo.smooth; infer_instance)
    | (haveI := Xo.smooth; haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s; infer_instance)

theorem cspD_local (Xo : Moduli Dw l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → Xo.XF c), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have hsm := cspD_smooth Xo c
  have h1 := HasRingHomProperty.appLE (P := @Smooth)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp; trivial)
  let ψ : c.F →+* Γ(Xo.XF c, V) :=
    ((pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)).appLE ⊤ V (fun p _ => by simp; trivial)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra c.F Γ(Xo.XF c, V) := ψ.toAlgebra
  have : Algebra.Smooth c.F Γ(Xo.XF c, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := c.F)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) c.F) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) c.F) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem cspD_comp_disj (Xo : Moduli Dw l) (c : Coeff l) (Z Z' : Comp Xo c) (hne : Z ≠ Z') :
    Disjoint (Z : Set (Xo.XF c)) Z' := cspD_disj (cspD_local Xo c) Z Z' Z.2 Z'.2 (fun h => hne (Subtype.ext h))

end Formalism.L2.Pj.CompSplitPfD
end
end

section



noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def IntFramesSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L → ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    (letI := io.toAlgebra; ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1)

def GenFibreSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt),
      ∃ (t' : SAB H (Sp T.Fr)) (_m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _))
        (_m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), True

def LieFreeSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X)
    (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) →
    letI := io.toAlgebra
    ∀ u₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left),
    (∀ τ i, IsTanAt x (u₀ τ i)) → (∀ τ i, IsEigAt c τ (u₀ τ i)) →
    (∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x (u₀ τ) a w) →
    ∃ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
      (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
      ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧
        (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
          ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧
        ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = u τ i ∧
          u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) ∧
      (∀ τ i, IsTanAt x (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧
      (∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x (u τ) a w) ∧
      ∀ τ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x (u₀ τ) cf (u τ i)

def ThetaFrameSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L → ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp T.Fr))
      (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _)) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      letI := io.toAlgebra
      ∀ s₀ : LB.Sec (PPx (z ≫ pullback.fst _ _)),
      (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i, s'.f i = scal (z ≫ pullback.fst _ _) a i * s₀.f i) →
      ∃ (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx (z ≫ pullback.fst _ _))),
        (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
          σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
        (∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ))
          (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
          RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧
          ∀ g : t'.G.left ⟶ Gx (z ≫ pullback.fst _ _),
            g ≫ (snd (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = m1.φ →
            g ≫ (fst (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = t'.G.hom →
            ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx (z ≫ pullback.fst _ _)).U (fun _ => j PUnit.unit)),
              s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
        (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i,
          s'.f i = scal (z ≫ pullback.fst _ _) a i * s.f i) ∧
        ∃ a : T.Frˣ, ∀ i, s.f i = scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i

def SpreadSt : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

theorem genFibre (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) : GenFibreSt Xo c := by
  intro T io O _ β Y yt z h1 h2 G m
  obtain ⟨PP', cub, sym, adj, prim, m2, -⟩ := sabPull hC (spMap (algebraMap T.V T.Fr)) G
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ yt _ m m2
  rw [← h1] at n
  have n' : SABMap _ Y.t (z ≫ (Y.jQ ≫ pullback.fst _ _)) := n
  obtain ⟨m1, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t _ _ z Y.m n'
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ _ z Y.m0.toSABMap m1
  exact ⟨_, n2, m2, trivial⟩



theorem intFrames_of (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hG : GenFibreSt Xo c) (hL : LieFreeSt Xo c)
    (hT : ThetaFrameSt Xo c) (hS : SpreadSt Xo c) : IntFramesSt Xo c := by

  have e : ∀ (X : Scheme.{0}) (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (v : Γ(X, U)),
      (Scheme.Hom.appLE (𝟙 X) U U h).hom v = v := by
    intro X U h v
    simp [Scheme.Hom.appLE]
    first
      | (erw [Category.id_comp, CategoryTheory.Functor.map_id]; rfl)
      | (erw [Category.id_comp, CategoryTheory.Functor.map_id]; simp; done)
      | (erw [CategoryTheory.Functor.map_id]; simp; done)
  have key : ∀ {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s s0 : LB.Sec (PPx x)) (a : S),
      (∀ i, s.f i = scal x a i * s0.f i) → ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
        (h : (PPx x).U i ≤ (𝟙 (Gx x)) ⁻¹ᵁ (PPx x).U i),
        (Scheme.Hom.appLE (𝟙 (Gx x)) _ _ h).hom (scal x a i * s0.f i) = s.f i := by
    intro S _ x s s0 a ha i h
    rw [ha i]
    exact e _ _ _ _
  intro T io O _ β Y hP yt z h1 h2
  letI := io.toAlgebra
  intro y₀ hy₀
  obtain ⟨x0, hx0, u0, tan0, eig0, basis0, s0, gen0⟩ := y₀
  dsimp only at hy₀
  subst hy₀
  obtain ⟨PP', cub, sym, adj, prim, mG, -⟩ := sabPull hC yt Y.t
  obtain ⟨t', m1, m2, -⟩ := hG T io O β Y yt z h1 h2 _ mG
  obtain ⟨ub, u, ⟨hub1, hub2, hub3, hub4⟩, hu1, hu2, hu3, hu4⟩ :=
    hL T io _ t' _ m1 m2 hx0 u0 tan0 eig0 basis0
  obtain ⟨θ, s, hθ1, hθ2, hs, a, ha⟩ := hT T io O β Y hP yt z h1 h2 _ mG t' m1 m2 s0 gen0
  choose cf hcf1 hcf2 hcf3 using hu4
  let y : FrPt Xo c T.Fr :=
    { x := _, x_over := hx0, u := u, tan := hu1, eig := hu2, basis := hu3, s := s, gen := hs }
  refine ⟨⟨y, hS T.Fr y, _, t', m1, m2, ⟨ub, hub1, hub2, hub3, hub4⟩, θ, hθ1, hθ2⟩,
    fun k => match k with | none => a | some p => (hcf1 p.1 p.2).unit, rfl, ?_, 𝟙 _, ?_, ?_, ?_⟩
  · intro τ i
    exact ⟨cf τ i, (hcf1 τ i).unit_spec.symm, hcf2 τ i, hcf3 τ i⟩
  · exact Category.id_comp _
  · exact Category.id_comp _
  · exact key _ s s0 _ ha

theorem intFrames (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hL : LieFreeSt Xo c) (hT : ThetaFrameSt Xo c)
    (hS : SpreadSt Xo c) : IntFramesSt Xo c :=
  intFrames_of Xo c hC (genFibre Xo c hC) hL hT hS

end Formalism.L2.Pj
end
end
