module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ZM.SiegPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lbIso_pull_comp {X Y Y' : Scheme.{0}} {L : LB X} {A : LB Y} {F : Y ⟶ X} (H : LBIso A (L.pull F))
    (h : Y' ⟶ Y) : LBIso (A.pull h) (L.pull (h ≫ F)) := by
  refine LBIso.chartPull (chartPullPull A h h rfl) ⟨id, fun J x hx => ?_, fun y J J' hJ hJ' => ?_⟩ H
  · have hx' := (mem_pull (F := h ≫ F)).1 hx
    exact (mem_pull (F := F)).2 hx'
  · have a1 := (mem_pull (F := h ≫ F)).1 hJ
    have a2 := (mem_pull (F := h ≫ F)).1 hJ'
    rw [gm_pull_g L (h ≫ F) (𝟙 Y') y J J' hJ hJ', Category.id_comp]
    exact (gm_pull_g L F h y J J' ((mem_pull (F := F)).2 a1) ((mem_pull (F := F)).2 a2)).symm

theorem exists_isSquare {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (w : φ ≫ G.hom = G'.hom ≫ f) :
    ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ := by
  let T : Over S := Over.mk ((G' ⊗ G').hom ≫ f)
  have w₁ : ((fst G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (fst G' G')]
    rfl
  have w₂ : ((snd G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (snd G' G')]
    rfl
  let x : T ⟶ G := Over.homMk ((fst G' G').left ≫ φ) w₁
  let y : T ⟶ G := Over.homMk ((snd G' G').left ≫ φ) w₂
  refine ⟨(lift x y).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Over.comp_left, lift_snd]
    rfl

theorem isSquare_tensor {G G' : Over S} (φ : G' ⟶ G) : IsSquare φ.left (φ ⊗ₘ φ).left := by
  constructor
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem isSquare_comp {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  constructor
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem isSquare_unique {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') (e : φ = φ') : φ₂ = φ₂' := by
  subst e
  have w : φ₂' ≫ (G ⊗ G).hom = φ₂ ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, h'.1, ← Category.assoc, h.1]
  let a : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let b : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' w
  have hab : a = b := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (fst G G).left = φ₂' ≫ (fst G G).left
      rw [h.1, h'.1]
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (snd G G).left = φ₂' ≫ (snd G G).left
      rw [h.2, h'.2]
  exact congrArg (fun m => m.left) hab

theorem lbIso_lam_pull {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (h : IsGrpPullback G' G f φ)
    (hw : LBIso L' (L.pull φ)) {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) :
    LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain ⟨w, hw'⟩ := hw
  have hP : PGen w := by
    unfold PGen gw
    intro Y g y j j' k k' h1 h2 h3 h4
    have m1 : g y ∈ (L.pull φ).U (fun _ => j) := (mem_pull (F := φ)).2 h1
    have m2 : g y ∈ (L.pull φ).U (fun _ => j') := (mem_pull (F := φ)).2 h2
    have hV : g y ∈ (L.pull φ).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull φ).U (fun _ => j') ⊓ L'.U k') :=
      ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
    have e := congrArg (gm g y _) (hw' (fun _ => j, k) (fun _ => j', k'))
    unfold LB.div at e
    simp only [map_mul, map_inv] at e
    simp only [gm_res g y _ hV] at e
    rw [gm_pull_g L φ g y (fun _ => j) (fun _ => j') m1 m2] at e
    exact e
  have e : ∀ I : ULift (Finset (Fin 2)),
      (psum G' (x2 G') I.down).left ≫ φ = φ₂ ≫ (psum G (x2 G) I.down).left := by
    let T : Over S' := G' ⊗ G'
    have hj : φ₂ ≫ (G ⊗ G).hom = T.hom ≫ f := by
      rw [← Over.w (fst G G), ← Category.assoc, hs.1, Category.assoc, h.1.w, ← Category.assoc,
        Over.w (fst G' G')]
    let U : Over S := Over.mk (T.hom ≫ f)
    let j : U ⟶ G ⊗ G := Over.homMk φ₂ hj
    have hΦ : ∀ u : T ⟶ G', (u.left ≫ φ) ≫ G.hom = U.hom := fun u => by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u]
      rfl
    let Φ : (T ⟶ G') → (U ⟶ G) := fun u => Over.homMk (u.left ≫ φ) (hΦ u)
    have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y =>
      Over.OverMorphism.ext (h.2 T x y (Φ x) (Φ y) rfl rfl).symm
    let Φh : (T ⟶ G') →* (U ⟶ G) := MonoidHom.mk' Φ Φmul
    have key : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), Φ u = j ≫ v → u.left ≫ φ = φ₂ ≫ v.left :=
      fun u v hh => congrArg (fun m => m.left) hh
    have key' : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), u.left ≫ φ = φ₂ ≫ v.left → Φ u = j ≫ v :=
      fun u v hh => Over.OverMorphism.ext (by exact hh)
    have base : ∀ k : Fin 2, Φ (x2 G' k) = j ≫ x2 G k := by
      intro k
      fin_cases k
      · exact key' _ _ hs.1.symm
      · exact key' _ _ hs.2.symm
    have fold : ∀ l : List (Fin 2),
        Φ (List.foldr (fun k acc => padd G' (x2 G' k) acc) (pzero G' (G2 G')) l) =
          j ≫ List.foldr (fun k acc => padd G (x2 G k) acc) (pzero G (G2 G)) l := by
      intro l
      induction l with
      | nil =>
        change Φh 1 = j ≫ 1
        rw [map_one, comp_one]
      | cons k l ih =>
        change Φ (x2 G' k * _) = j ≫ (x2 G k * _)
        rw [Φmul, comp_mul, base k, ih]
    intro I
    exact key _ _ (fold _)
  exact LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ₂ _ e) (iso_linComb hP _ _)

end GlobalTheory.ZM.SiegPull


end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

theorem exists_uniformisation_at_point : ThetaUnifAV → Out.Laws → (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF → (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) → (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') ∧ (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro hT _ _ hPull hPol hDat E _ _ _ H D l Xo σ g ty _ hσ hty y hy
  let b' : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := σ (baseKA l).ρ
      ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  obtain ⟨o, ⟨m⟩⟩ := hPull E H D l (KA l) ℂ (baseKA l) b' σ Xo.X (Sp ℂ) Xo.s (𝟙 _) y rfl rfl
    (hy.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨hab, hsm, hrig, hsym⟩ := hPol E H D l ℂ b' (Sp ℂ) (𝟙 _) o
  obtain ⟨rig, hr⟩ := id hrig
  obtain ⟨u, Hm, χ, Ef, hAH, -, h1, h2, hF, -, hE, hbij, hweil⟩ :=
    hT { A := o.t.G, isAb := hab, g := _, smoothDim := hsm, L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := hrig,
         sym := hsym, ample := o.ample, ktriv := o.ktriv } rig hr
  have hLiso : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push m.cart (𝟙_ _)
    (weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ Xo.univ.t.PP.isLB o.t.PP.isLB m.cart hLiso _) y (Category.id_comp y)
  have he₀ := isExp_push m.cart u h1 h2 Φ hΦ
  have hker₀ : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep Xo.univ.t.act u.Λ u.discrete hker₀ fun a => by
    obtain ⟨F, hF⟩ := hF (o.t.act.act a) (o.t.act.hom a)
    refine ⟨F, fun z => Over.OverMorphism.ext ?_⟩
    rw [hΦ, hF, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  obtain ⟨hdet, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ y σ hy
  obtain ⟨h, hh⟩ := exists_equiv_of_finrank_eq (isSplitting_embeddings (E := E)) (diagRep ty) ρ fun φ => by
    rw [finrank_eigenSub_diagRep]
    by_cases hφ : φ (H.rt : E) = H.rt0
    · rw [(hty φ).1 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).1 (hφ.trans hσ.symm))]
    · rw [(hty φ).2 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).2 fun h => hφ (h.trans hσ))]
  have he := he₀.comp_equiv h
  have hlin : ∀ (a : 𝓞 E) z, Φ (u.ex (h fun k => ty k (a : E) * z k)) = Φ (u.ex (h z)) ≫ Xo.univ.t.act.act a :=
    fun a z => by rw [← hρ, ← hh, diagRep_apply]
  have hst : ∀ a, ∀ x ∈ u.Λ, ρ a x ∈ u.Λ := fun a x hx => by
    have := Xo.univ.t.act.hom a
    rw [← hker₀, hρ, (hker₀ x).2 hx, MonObj.one_comp]
  letI : SMul (𝓞 E) u.Λ := ⟨fun a x => ⟨ρ a x, hst a x x.2⟩⟩
  have hsm : ∀ (a : 𝓞 E) (x : u.Λ), ((a • x : u.Λ) : _ → ℂ) = ρ a x := fun _ _ => rfl
  letI : Module (𝓞 E) u.Λ := Module.ofMinimalAxioms
    (fun a x y => Subtype.ext (by simp [hsm])) (fun a b x => Subtype.ext (by simp [hsm]))
    (fun a b x => Subtype.ext (by simp [hsm])) (fun x => Subtype.ext (by simp [hsm]))
  let P : u.Λ →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp u.Λ.subtype.toAddMonoidHom
  have hP : ∀ x, h (P x) = x := fun x => h.apply_symm_apply _
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ u.Λ := fun z =>
    ⟨by rintro ⟨x, rfl⟩; rw [hP]; exact x.2, fun hz => ⟨⟨_, hz⟩, h.symm_apply_apply z⟩⟩
  have hker : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P.range := fun z => (hker₀ _).trans (hrange z).symm
  have hPs : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x => congrFun (h.injective (by
    rw [hP, hsm, ← diagRep_apply, hh, hP]))
  have hPi : Function.Injective P := h.symm.injective.comp Subtype.val_injective
  have hPd : DiscreteTopology P.range := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (f := fun z : P.range => (⟨h z, (hrange _).1 z.2⟩ : u.Λ))
      ((h.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _) fun z w hzw => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hzw))
  have hPf : Submodule.span ℝ (Set.range P) = ⊤ := by
    have e : Set.range P = (h.symm.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
    rw [e, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  obtain ⟨Hm', hH', hH''⟩ := exists_hermForm_comp Hm hAH.1 h.toLinearMap
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re := fun z hz => by
    rw [hH'']
    exact hAH.2.1 _ (h.map_ne_zero_iff.2 hz)
  have him : ∀ x x', (hermForm Hm' (P x) (P x')).im = Ef x x' := fun x x' => by
    rw [hH'', hE]
    exact congrArg₂ (fun a b => (hermForm Hm a b).im) (hP x) (hP x')
  have hweil' : ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P b))))
        (unitOn c) := fun k a b c hk hc => by
    rw [map_smul, map_smul, hP, hP]
    exact hΦW _ _ _ _ (hweil k a b c hk hc)
  obtain ⟨D', ε, hp, hq, hε⟩ := hDat E H u.Λ Ef D.p D.q g ty P Hm' hty hbij
    (adj_of_tateIso Xo.univ.t.PP.isLB he hker hPs hlin hweil' I) hPs hPi hPd hPf hH' hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp ε.toLinearMap.toAddMonoidHom
  have hr' : P'.range = P.range := by
    ext z
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨ε x, rfl⟩,
      by rintro ⟨x, rfl⟩; exact ⟨ε.symm x, congrArg P (ε.apply_symm_apply x)⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hPi.comp ε.injective, hr' ▸ hPd, ?_, Hm', hH', hpos, fun x x' => ?_⟩
    · exact (congrArg (fun x => P x i) (map_smul ε a x)).trans (hPs a _ i)
    · rw [← AddMonoidHom.coe_range, hr', AddMonoidHom.coe_range, hPf]
    · rw [hε]; exact him _ _
  have hker' : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P'.range := hr' ▸ hker
  have hweil'' : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P' a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P' b))))
        (unitOn c) := fun k a b c hk hc => hweil' k (ε a) (ε b) c hk (by rw [hc, hε])
  obtain ⟨f, ν, f1, f2, f3, f4, f5⟩ := similar_with_multiplier
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I
    (expTateIso he hper hker' hlin hweil'')
  have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  refine ⟨D', f l.M', P', fun z => Φ (u.ex (h z)), ⟨hp, hq, f, ν, f1, f2, f3, ?_, rfl⟩, hy, hper, he, hker', hlin,
    hweil'', fun a ha => (hM a ha).trans (f5 _ _ hM' (Nat.dvd_lcm_left _ _) a),
    fun a => (hA a).trans (f5 _ _ hM' (Nat.dvd_lcm_right _ _) a)⟩
  rw [← hζ, f4 _ l.A_pos]
  exact expNegUnit_zpow_val _ _

end GlobalTheory.PointUnif
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.holomorphic_map_moduli_lifts_locally_to_periods : ThetaUnifAV → Out.Laws → (∀ (k
    : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ GlobalTheory.IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S'
    : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G
    : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀
    : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z
    + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧
    (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e
    : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r
    : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin
    m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e
    b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧
    (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β
    : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀
    : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x
    w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g →
    ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w) → (∀ (La
    : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m →
    ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin
    g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b
    : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds
    b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b
    i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P
    b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P
    b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P
    b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range) → (∀ (O
    : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+*
    Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ]
    O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B'
    : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin
    g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h
    b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a)) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (m k : ℕ) (B : Set (Fin m → ℂ)) (y
    : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ P.A) (c : ℂˣ) (b₀
    : Fin m → ℂ), 0 < k → IsUnit (k : Γ(X,
    ⊤)) → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x
    b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ =
    x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs P.A P.L k (x b₀) (x' b₀) (unitOn c) →
    ∀ b ∈ B, Out.WeilIs P.A P.L k (x b) (x' b) (unitOn c)))) → ∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g →
    ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀
    ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range)
    ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a
    a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂
    : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B'
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a))) := by
  first | exact @GlobalTheory.LocLift.holomorphic_map_lifts_to_periods | exact GlobalTheory.LocLift.holomorphic_map_lifts_to_periods | (intros; apply GlobalTheory.LocLift.holomorphic_map_lifts_to_periods <;> assumption)
end
