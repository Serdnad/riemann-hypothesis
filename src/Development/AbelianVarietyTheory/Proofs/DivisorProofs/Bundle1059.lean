module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.cuspidal_galois_pairing_eq_pm_one_prime_degree : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k n : ℕ, 0 < m → n = Module.finrank F F' * m → Reg (Nat.card F) n k → ∃ z : ℤ, (z = 1 ∨ z = -1) ∧ ∑ᶠ x, psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n x * star (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n x) = z * (Nat.card (GL (Fin n) F') : ℂ) := by
  first | (exact @GlobalTheory.Shin.PairPM.pairing_pm_one) | (exact GlobalTheory.Shin.PairPM.pairing_pm_one) | (intros; apply GlobalTheory.Shin.PairPM.pairing_pm_one  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThinGlue

variable {X : Scheme.{0}}

theorem res_res {U W W' : X.Opens} (h : W ≤ U) (h' : W' ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {W : X.Opens} (x y : Γ(X, W)ˣ)
    (h : ∀ p ∈ W, ∃ (W' : X.Opens) (hW : W' ≤ W), p ∈ W' ∧ res hW x = res hW y) : x = y := by
  choose W' hW hp hxy using h
  ext
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => W' p.1 p.2) W (fun p => homOfLE (hW p.1 p.2)) ?_ _ _ ?_
  · intro p hpW
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hpW⟩, hp _ hpW⟩
  · intro p
    have := congrArg Units.val (hxy p.1 p.2)
    exact this

end GlobalTheory.ThinGlue

namespace GlobalTheory.ThinGlue

theorem exists_lb_frame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  intro X C _ V hV _ u hB hC
  have hE := fun T₁ T₂ => GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis X C V hV u hB hC T₁ T₂
  choose g hg using fun T₁ T₂ => (hE T₁ T₂).exists
  have key : ∀ (T₁ T₂ S : C) (a : T₁ ⟶ S) (b : T₂ ⟶ S) (h : V S ≤ V T₁ ⊓ V T₂),
      res h (g T₁ T₂) * u T₁ S a = u T₂ S b := fun T₁ T₂ S a b _ => hg T₁ T₂ S a b
  have bas2 : ∀ (i j : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S, ⟨a⟩, ⟨b⟩, hpS, hSW⟩ := hB.2 i j p W hp (hW hp).1 (hW hp).2
    exact ⟨V S, hSW, hpS, h S a b hSW⟩
  have bas3 : ∀ (i j k : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j ⊓ V k) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (_ : k ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j k W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S₀, ⟨a⟩, ⟨b⟩, hpS₀, hS₀W⟩ := hB.2 i j p W hp (hW hp).1.1 (hW hp).1.2
    obtain ⟨S, ⟨c⟩, ⟨d⟩, hpS, hSW⟩ := hB.2 S₀ k p W hp hpS₀ (hW hp).2
    exact ⟨V S, hSW, hpS, h S (a ≫ c) (b ≫ c) d hSW⟩
  have gself : ∀ T, g T T = 1 := fun T =>
    (hE T T).unique (hg T T) (fun S a b => by rw [Subsingleton.elim a b, map_one, _root_.one_mul])
  let L : LB X := ⟨C, V, g⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨t, hp, _⟩ := hB.1 p ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, hp⟩
  · intro T
    show res _ (g T T) = 1
    rw [gself, map_one]
  · intro i j k
    refine bas3 i j k _ le_rfl _ _ fun S a b c hS => ?_
    show res hS (res _ (g i j) * res _ (g j k)) = res hS (res _ (g i k))
    simp only [map_mul, res_res]
    have e1 := key i j S a b (hS.trans inf_le_left)
    have e2 := key j k S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    have e3 := key i k S a c (hS.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    apply mul_right_cancel (b := u i S a)
    rw [e3, mul_comm (res _ (g i j)), _root_.mul_assoc, e1, e2]
  · refine ⟨fun T m => res (le_of_eq (inf_comm _ _)) (g m T), fun T => ?_, ?_⟩
    · intro m m'
      refine bas3 T m m' _ le_rfl _ _ fun S a b c hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (g m m') * res _ (res _ (g m' T)))
      simp only [map_mul, res_res]
      have e1 := key m T S b a (hS.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))
      have e2 := key m m' S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      have e3 := key m' T S c a (hS.trans (le_inf inf_le_right (inf_le_left.trans inf_le_left)))
      apply mul_right_cancel (b := u m S b)
      rw [e1, mul_comm (res _ (g m m')), _root_.mul_assoc, e2, e3]
    · intro T T' a m
      refine bas2 T' m _ le_rfl _ _ fun S c d hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (u T T' a) * res _ (g m T'))
      simp only [map_mul, res_res]
      have e1 := key m T S d (a ≫ c) (hS.trans (le_inf inf_le_right ((inf_le_left.trans (hV a)))))
      have e2 := key m T' S d c (hS.trans (le_inf inf_le_right inf_le_left))
      have e3 := hC a c
      apply mul_right_cancel (b := u m S d)
      rw [e1, _root_.mul_assoc, e2, e3]

end GlobalTheory.ThinGlue
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameCob

theorem res_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl

theorem comm_group_step {G : Type*} [CommGroup G] (a b c d e f g k : G) (A : a * b = c * d) (B : b = e * f)
    (C : d = g * k) : e * a * g⁻¹ * f = c * k := by
  subst B C
  calc e * a * g⁻¹ * f = g⁻¹ * (a * (e * f)) := by ac_rfl
    _ = g⁻¹ * (c * (g * k)) := by rw [A]
    _ = c * k := by rw [mul_left_comm c, inv_mul_cancel_left]

theorem frames_cohomologous : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X)
    (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → L'.IsLB → LBIso L L' →
    IsFrame L V hV u → IsFrame L' V hV u' →
    ∃ t : ∀ T : C, Γ(X, V T)ˣ, ∀ T T' a, u' T T' a * res (hV a) (t T) = t T' * u T T' a := by
  intro X C _ V hV L L' u u' hL hL' ⟨w, hw⟩ ⟨τ, hτg, hτ⟩ ⟨τ', hτ'g, hτ'⟩
  choose t ht htu using fun T => GlobalTheory.T.existsUnique_unit_ratio_generators_isomorphic_lineBundles X L L' (V T) w (τ T) (τ' T) hL hL' hw (hτg T) (hτ'g T)
  refine ⟨t, fun T T' a => ?_⟩
  have key : u' T T' a * res (hV a) (t T) * (u T T' a)⁻¹ = t T' := by
    refine htu T' _ (fun m m' => ?_)
    have hO : V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T ⊓ (L'.U m' ⊓ L.U m) := inf_le_inf_right _ (hV a)
    have A := congrArg (res hO) (ht T m m')
    have B := congrArg (res (inf_le_inf_left (V T') inf_le_left :
      V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T' ⊓ L'.U m')) (hτ' T T' a m')
    have C' := congrArg (res (inf_le_inf_left (V T') inf_le_right :
      V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T' ⊓ L.U m)) (hτ T T' a m)
    simp only [map_mul, map_inv, res_comp] at A B C' ⊢
    erw [res_comp] at A
    exact comm_group_step _ _ _ _ _ _ _ _ A B C'
  rw [← key, inv_mul_cancel_right]

end GlobalTheory.FrameCob
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundle_obstruction_zero_of_restriction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L : LB X), IsPullback i s₀ s (spMap π) → L.IsLB → IsObL S α (L.pull i) 0 := by
  first | exact @GlobalTheory.LBObs.isObL_pull_zero | exact GlobalTheory.LBObs.isObL_pull_zero | (intros; apply GlobalTheory.LBObs.isObL_pull_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

variable {R₀ : Type} [CommRing R₀] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}
  {C D : Type} [Category.{0} C] [Category.{0} D]

theorem opOf_le_of_natTrans (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (θ : H ⋙ G ⟶ K) (T : D) :
    opOf K T ≤ opOf G (H.obj T) := leOfHom (θ.app T).unop

def natCoef (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (θ : H ⋙ G ⟶ K) :
    CoefMap (RingHom.id R₀) (G ⋙ OAff s₀) (K ⋙ OAff s₀) where
  G := H
  α T := (mp (OAff s₀) (θ.app T)).toRingHom
  naturality {T T'} φ b := by
    change mp (OAff s₀) (θ.app T') (mp (OAff s₀) ((H ⋙ G).map φ) b) = mp (OAff s₀) (K.map φ) (mp (OAff s₀) (θ.app T) b)
    rw [← mp_comp, ← mp_comp, θ.naturality φ]
  smul T r b := by
    change mp (OAff s₀) (θ.app T) (r • b) = r • mp (OAff s₀) (θ.app T) b
    exact map_smul _ r b

theorem obAt_refine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)
    (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀)))
    (C D : Type) [Category.{0} C] [Category.{0} D] (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C)
    (_ : H ⋙ G ⟶ K), ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) →
      ObAt S α L K ((extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L c C D _ _ G K H θ h
  obtain ⟨u, hf, ho⟩ := h
  refine ⟨fun T T' a ↦ res (opOf_le_of_natTrans G K H θ T') (u _ _ (H.map a)), ?_, ?_⟩
  · exact GlobalTheory.T.isLineBundleFrameOnBasis_restrict_finer_opens X₀ C (opOf G) (opOf_le G) L u D (opOf K) (opOf_le K) H (opOf_le_of_natTrans G K H θ) hf
  · have key := GlobalTheory.T.unitCocycleLiftObstruction_pullback_naturality R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) D (K ⋙ OAff s₀)
      ((ofSys S).restrict K) (natCoef (s₀ := s₀) G K H θ) (fun T ↦ mp S.F (θ.app T)) u
      (fun T T' a ↦ res (opOf_le_of_natTrans G K H θ T') (u _ _ (H.map a)))
      ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c)
      (fun T b ↦ S.nat (θ.app T) b)
      (fun T T' a b ↦ by
        change mp S.F (K.map a) (mp S.F (θ.app T) b) = mp S.F (θ.app T') (mp S.F ((H ⋙ G).map a) b)
        exact (mp_comp S.F _ _ b).symm.trans
          ((congrArg (fun f ↦ mp S.F f b) (θ.naturality a).symm).trans (mp_comp S.F _ _ b)))
      (fun T T' a ↦ rfl) ho
    have hc : (extMap R₁ (natCoef (s₀ := s₀) G K H θ)).pull2 ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) =
        (extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c := by
      rw [← CoefMap.pullCohomologyTwo_comp]
      refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ (fun T b ↦ ?_) c
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [← hc]
    exact key

end GlobalTheory.LBObs
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.ObEx

theorem exists_isObL : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L hL
  obtain ⟨C, _, _, G, u, hB, hF⟩ := GlobalTheory.T.exists_lineBundle_frame_thin_affine_basis X₀ L hL
  have hc := GlobalTheory.T.isMultiplicativeOneCocycleOpens_of_isLineBundleFrameOnBasis X₀ C (opOf G) (opOf_le G) L u hL hF
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_unitCocycleLiftObstruction R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) u
    ((ofSys_isFun S).restrict G) (fun T T' T'' a b ↦ congrArg Units.val (hc a b))
  obtain ⟨c, rfl⟩ := (GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X₀ s₀ C G hB.1 hB.2).2.2 d
  exact ⟨c, C, inferInstance, inferInstance, G, hB, u, hF, hd⟩

end GlobalTheory.LBObs.ObEx
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.isIso_isogeny_omega_and_dual_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → Function.Surjective (omegaMap G H q) → Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  first | exact @GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | exact GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | (intros; apply GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigCap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def keep (π : CuspSub E a) : Subalgebra ℂ (Module.End ℂ (Sm E a)) where
  carrier := {z | ∀ φ ∈ π.V, z φ ∈ π.V}
  mul_mem' := fun hx hy φ h => hx _ (hy φ h)
  add_mem' := fun hx hy φ h => π.V.add_mem (hx φ h) (hy φ h)
  algebraMap_mem' := fun c φ h => π.V.smul_mem c h

def res (π : CuspSub E a) : keep π →ₐ[ℂ] Module.End ℂ π.V where
  toFun z := z.1.restrict z.2
  map_one' := LinearMap.ext fun φ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun φ => Subtype.ext rfl
  map_zero' := LinearMap.ext fun φ => Subtype.ext rfl
  map_add' _ _ := LinearMap.ext fun φ => Subtype.ext rfl
  commutes' _ := LinearMap.ext fun φ => Subtype.ext rfl

theorem Eop_mem (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) : Eop τ i j ∈ keep π := by
  have h : ∀ X, lie E a X ∈ keep π := fun X φ hφ => π.stable (.lie X) φ hφ
  exact (keep π).smul_mem ((keep π).sub_mem (h _) ((keep π).smul_mem (h _) _)) _

theorem res_Eop (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) :
    res π ⟨Eop τ i j, Eop_mem π τ i j⟩ = cx τ (lieOp π) i j := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  rfl

end GlobalTheory.WigCap


open GlobalTheory.WigCap in
theorem GlobalTheory.capelli_cuspSub : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (χ : Fin a → ℂ), π.HasInfChar τ (Multiset.map χ Finset.univ.val) → GlRel (cx τ (lieOp π)) ∧ ∀ u : ℂ, qdet (cx τ (lieOp π)) (u + ((a : ℂ) - 1) / 2) = algebraMap ℂ _ (∏ s, (u + χ s)) := by
  intro E _ _ _ a π τ χ hχ
  let X : Fin a → Fin a → keep π := fun i j => ⟨Eop τ i j, Eop_mem π τ i j⟩
  have hX : (fun i j => res π (X i j)) = cx τ (lieOp π) := funext fun i => funext fun j => res_Eop π τ i j
  have hval : (fun i j => (keep π).val (X i j)) = Eop τ := rfl
  constructor
  · intro i j k l
    have h := glRel_Eop (a := a) τ i j k l
    rw [← hX]
    simp only
    have h2 : X i j * X k l - X k l * X i j = (if j = k then X i l else 0) - (if l = i then X k j else 0) := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul]
      rw [h]
      split_ifs <;> rfl
    rw [← map_mul, ← map_mul, ← map_sub, h2, map_sub]
    split_ifs <;> simp
  · intro u
    rw [← hX, ← map_qdet]
    refine LinearMap.ext fun φ => Subtype.ext ?_
    have e1 : ((keep π).val (qdet X (u + ((a : ℂ) - 1) / 2))) = cap τ u := by
      rw [map_qdet, hval]; rfl
    change ((keep π).val (qdet X (u + ((a : ℂ) - 1) / 2))) φ.1 = _
    rw [e1, hχ.2 u φ.1 φ.2, Multiset.map_map, Finset.prod_eq_multiset_prod]
    simp [Algebra.algebraMap_eq_smul_one]
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FamCalc

variable {S : Scheme.{0}} {A : Over S}

theorem whisker_eq {Y T : Over S} (y : Y ⟶ T) : A ◁ y = lift (fst A Y) (snd A Y ≫ y) := by
  ext <;> simp

theorem lift_whisker {Y T Z : Over S} (y : Y ⟶ T) (a : Z ⟶ A) (t : Z ⟶ Y) :
    lift a t ≫ A ◁ y = lift a (t ≫ y) := by
  ext <;> simp

theorem pull_whisker_evc {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) (a : Z ⟶ A)
    (t : Z ⟶ Y) :
    CechPic.pull (lift a t).left (CechPic.pull (A ◁ y).left (cls N hN)) = evc hN a (t ≫ y) := by
  rw [← pull_comp, ← Over.comp_left, lift_whisker, evc]

theorem evc_whisker {T Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) :
    evc hN (fst A Y) (snd A Y ≫ y) = CechPic.pull (A ◁ y).left (cls N hN) := by
  rw [evc, whisker_eq]

theorem evc_ev_whisker {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T)
    (h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB) (a : Z ⟶ A) (t : Z ⟶ Y) :
    evc h a t = evc hN a (t ≫ y) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

theorem famCalc : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], (∀ (T Y : Over S) (N : LB (A ⊗ T).left) (y : Y ⟶ T), Fam A N → Fam A (ev N (fst A Y) (snd A Y ≫ y))) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : Fam A N) (hM : Fam A M) (y : Y ⟶ T) (u : Y ⟶ U) (D : LB (A ⊗ Y).left) (hD : D.IsLB), (cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) + GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB) ∨ cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) - GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB)) → Fam A D) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : N.IsLB) (hM : M.IsLB) (y : Y ⟶ T) (u : Y ⟶ U), Same A N M y u ↔ GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN) = GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) (z : Z ⟶ Y), N.IsLB → M.IsLB → Same A N M y u → Same A N M (z ≫ y) (z ≫ u)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (z : Z ⟶ Y) (u : Z ⟶ U), N.IsLB → M.IsLB → (Same A (ev N (fst A Y) (snd A Y ≫ y)) M z u ↔ Same A N M (z ≫ y) u)) := by
  intro S A _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T Y N y hN
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
    refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
    simp only [evc_ev_whisker hN.isLB y h]
    exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
  · intro T U Y N M hN hM y u D hD hc
    refine ⟨hD, (isAdditive_iff hD).2 fun Z a a' t ↦ ?_⟩
    have aN := (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
    have aM := (isAdditive_iff hM.isLB).1 hM.add Z a a' (t ≫ u)
    rcases hc with hc | hc
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) + evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_add (f := _), pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) - evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_sub, pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
  · intro T U Y N M hN hM y u
    rw [same_iff hN hM, evc_whisker, evc_whisker]
  · intro T U Y Z N M y u z hN hM h
    rw [same_iff hN hM] at h ⊢
    have e := congrArg (CechPic.pull (A ◁ z).left) h
    rwa [pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc] at e
  · intro T U Y Z N M y z u hN hM
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN _
    rw [same_iff h hM, same_iff hN hM, evc_ev_whisker hN y h, Category.assoc]

end GlobalTheory.FamCalc
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rep_ev_of_isPullback : ∀ (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S''), Rep A b P → IsPullback k b'' b h → Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  first | exact @GlobalTheory.DualCon.Rep.baseChange | exact GlobalTheory.DualCon.Rep.baseChange | (intros; apply GlobalTheory.DualCon.Rep.baseChange <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.finiteSetsInAffineOpen_finite_coproduct : ∀ {κ : Type} [Finite κ] (B : κ → Scheme.{0}), (∀ i, FinAff (B i)) → FinAff (∐ B) := by
  first | exact @GlobalTheory.DualCon.finAff_sigma | exact GlobalTheory.DualCon.finAff_sigma | (intros; apply GlobalTheory.DualCon.finAff_sigma <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_isEmpty : ∀ (S : Scheme.{0}) (A S' : Over S) [GrpObj A] (g : ℕ), IsEmpty S'.left → HasRepAF A g S' := by
  first | exact @GlobalTheory.DualCon.hasRepAF_of_isEmpty | exact GlobalTheory.DualCon.hasRepAF_of_isEmpty | (intros; apply GlobalTheory.DualCon.hasRepAF_of_isEmpty <;> assumption)
end
