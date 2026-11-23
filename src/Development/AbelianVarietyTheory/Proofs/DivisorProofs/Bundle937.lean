module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle914
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_connected_etale_splitting_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), ∃ (G₀ G₁ : PDivGroup p k) (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (i₁ : G₁ ⟶ G) (q₁ : G ⟶ G₁), G₀.IsConn ∧ G₁.IsEt ∧ i₀ ≫ q₀ = 𝟙 G₀ ∧ i₁ ≫ q₁ = 𝟙 G₁ ∧ q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G := by
  first | exact @GlobalTheory.PDivGroup.exists_isConn_isEt_splitting | exact GlobalTheory.PDivGroup.exists_isConn_isEt_splitting | (intros; apply GlobalTheory.PDivGroup.exists_isConn_isEt_splitting <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_dualHom_eq_zero_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (f : G ⟶ H), G.IsEt → H.IsEt → rigExtMap f = 0 → rigExtMap (dualHom G H f) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt | exact GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt | (intros; apply GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_holomorphic_primitive_of_cechDeRham_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q, IsPer u.ex u.Λ x q → ∀ c, Hyp1.mk _ c = x → ∃ h, IsPrim u.ex c h ∧ ∀ (U : A.left.affineOpens) (l : u.Λ), ∀ z ∈ pre u.ex U.1, h U (z + l) = h U z + q l := by
  first | exact @GlobalTheory.CechPer.exists_prim_of_isPer | exact GlobalTheory.CechPer.exists_prim_of_isPer | (intros; apply GlobalTheory.CechPer.exists_prim_of_isPer <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_regular_section_of_regular_differences : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ U : A.left.affineOpens, ∃ k : (Fin g → ℂ) → ℂ, ∀ i, IsReg u.ex (U.1 ⊓ W i) (k - h i) := by
  first | exact @GlobalTheory.CechPer.exists_section_of_isReg_sub | exact GlobalTheory.CechPer.exists_section_of_isReg_sub | (intros; apply GlobalTheory.CechPer.exists_section_of_isReg_sub <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.le_iSup_of_uniformisationParameters_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  first | exact @GlobalTheory.CechPer.le_iSup_of_pre_cover | exact GlobalTheory.CechPer.le_iSup_of_pre_cover | (intros; apply GlobalTheory.CechPer.le_iSup_of_pre_cover <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformisedOneFormEvaluation_linear_pullback : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  first | exact @GlobalTheory.CechPer.evForm_secPull | exact GlobalTheory.CechPer.evForm_secPull | (intros; apply GlobalTheory.CechPer.evForm_secPull <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.evForm_restriction_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V) (ξ : Ω[Sec (str A) U.1⁄ℂ]), ∀ z ∈ pre u.ex V.1, evForm u.ex V.1 z (p1 (OAff (str A)) a ξ) = evForm u.ex U.1 z ξ := by
  first | exact @GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq | exact GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq | (intros; apply GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq <;> assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → Module.Free (Ainf p O) (latt G) ∧ Module.Finite (Ainf p O) (latt G) ∧ Module.finrank (Ainf p O) (latt G) = G.height := by
  first | exact @GlobalTheory.PDivLat.latt_free_finrank | exact GlobalTheory.PDivLat.latt_free_finrank | (intros; apply GlobalTheory.PDivLat.latt_free_finrank <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.geometric_tate_level_condition_descends_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  first | exact @GlobalTheory.UPel.HT.geom_descends_galoisCover | exact GlobalTheory.UPel.HT.geom_descends_galoisCover | (intros; apply GlobalTheory.UPel.HT.geom_descends_galoisCover; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), (Nonempty (ObjMap o'' o' f') → Nonempty (ObjMap o' o f) → Nonempty (ObjMap o'' o (f' ≫ f))) ∧ ∀ m : ObjMap o' o f, LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp_diag_lbIso | exact GlobalTheory.UPel.HT.objMap_comp_diag_lbIso | (intros; apply GlobalTheory.UPel.HT.objMap_comp_diag_lbIso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_harrisTaylorObjectPullback : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (f : S' ⟶ S), f ≫ s = s' → ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  first | exact @GlobalTheory.UPel.HT.BaseChange.exists_objMap | exact GlobalTheory.UPel.HT.BaseChange.exists_objMap | (intros; apply GlobalTheory.UPel.HT.BaseChange.exists_objMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem isGaloisCover_of_isPullback {X Y X' Y' : Scheme.{0}} {Ga Ga' : Type} [Group Ga] [Group Ga']
    {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y} {ρ' : Ga' → (X' ⟶ X')} {π' : X' ⟶ Y'} {u : X' ⟶ X} {v : Y' ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (one' : ρ' 1 = 𝟙 X') (mul' : ∀ a c, ρ' (a * c) = ρ' a ≫ ρ' c) (inj' : Function.Injective ρ')
    (hπ : ∀ a, ρ' a ≫ π' = π')
    (up : ∀ a', ∃ a, ρ' a' ≫ u = u ≫ ρ a) (down : ∀ a, ∃ a', ρ' a' ≫ u = u ≫ ρ a) :
    GlobalTheory.ZM.IsGaloisCover Ga' ρ' π' := by
  refine
    { finite := ?_
      one := one'
      mul := mul'
      inv := hπ
      fin := MorphismProperty.of_isPullback (P := @IsFinite) hp h.fin
      etale := MorphismProperty.of_isPullback (P := @Etale) hp h.etale
      onto := MorphismProperty.of_isPullback (P := @Surjective) hp h.onto
      fibre := ?_ }
  · have := h.finite
    choose σ hσ using up
    refine Finite.of_injective σ fun a c e => inj' ?_
    exact hp.hom_ext (by rw [hσ, hσ, e]) (by rw [hπ, hπ])
  · intro K _ _ y y' e
    obtain ⟨a, ha, ha'⟩ := h.fibre K (y ≫ u) (y' ≫ u) (by simp only [Category.assoc, hp.w, reassoc_of% e])
    obtain ⟨a', ea'⟩ := down a
    have ex : y ≫ ρ' a' = y' := hp.hom_ext
      (by rw [Category.assoc, ea', ← Category.assoc, ha])
      (by rw [Category.assoc, hπ, e])
    refine ⟨a', ex, fun b' hb' => inj' ?_⟩
    obtain ⟨b, eb⟩ := up b'
    have hb'' : y ≫ ρ' b' = y' := hb'
    have hb : b = a := ha' b (by show (y ≫ u) ≫ ρ b = y' ≫ u; rw [Category.assoc, ← eb, ← Category.assoc, hb''])
    subst hb
    exact hp.hom_ext (by rw [eb, ea']) (by rw [hπ, hπ])

end GlobalTheory.UPel.HT.Hecke.PullHecke

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem transl_one {S : Scheme.{0}} {A : Over S} [GrpObj A] : transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  show 𝟙 A * (toUnit A ≫ 1) = 𝟙 A
  rw [MonObj.comp_one, _root_.mul_one]

theorem transl_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    transl (a * c) = transl a ≫ transl c := by
  have e : transl a ≫ transl c = transl a * (toUnit A ≫ c) := by
    show transl a ≫ (𝟙 A * (toUnit A ≫ c)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (transl a ≫ toUnit A) (toUnit A)]
  rw [e]
  show 𝟙 A * (toUnit A ≫ (a * c)) = (𝟙 A * (toUnit A ≫ a)) * (toUnit A ≫ c)
  rw [MonObj.comp_mul, _root_.mul_assoc]

theorem transl_injective {S : Scheme.{0}} {A : Over S} [GrpObj A] {a c : 𝟙_ (Over S) ⟶ A}
    (h : (transl a).left = (transl c).left) : a = c := by
  have h' : transl a = transl c := Over.OverMorphism.ext h
  rw [← one_comp_transl a, h', one_comp_transl]

theorem grpScheme_square_hom_ext {S : Scheme.{0}} {A : Over S} {X : Scheme.{0}} (u u' : X ⟶ (A ⊗ A).left)
    (h₁ : u ≫ (fst A A).left = u' ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = u' ≫ (snd A A).left) : u = u' := by
  have hw : u' ≫ (A ⊗ A).hom = u ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, ← h₁, Category.assoc]
  let U : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk u rfl
  let U' : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk u' hw
  have : U = U' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂)
  exact congrArg (fun z => z.left) this

theorem grpSchemeSquareProductMap_comp_fst {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') : sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  show (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left ≫ _ = _
  rw [← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') : sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  show (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left ≫ _ = _
  rw [← Over.comp_left, lift_snd, Over.comp_left]

theorem cls_heckePow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB) :
    GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h = n • GlobalTheory.CechPic.cls L hL := by
  unfold GlobalTheory.UPel.HT.Hecke.lbPow at h ⊢
  rw [GlobalTheory.CechPic.cls_linComb hL]
  simp [GlobalTheory.CechPic.pull_id]

end GlobalTheory.UPel.HT.Hecke.PullHecke

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem isHecke_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R)
    (f : S' ⟶ S) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) (f ≫ s))
    (o₁' : Obj b N (f ≫ s)), IsHecke g c k N o o' ψ → ObjMap o₁ o f → ObjMap o₁' o' f →
    ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsHecke g c k N o₁ o₁' ψ₁ := by
  intro p _ D R _ b g c k N _ _ _ S S' s f o o' ψ o₁ o₁' hH m m'
  obtain ⟨hmon, hlin, heta, hgal, ⟨hP⟩, hdvd⟩ := hH
  have w : (m.φ ≫ ψ.left) ≫ o'.A.hom = o₁.A.hom ≫ f := by
    rw [Category.assoc, Over.w]; exact m.cart.1.w
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk (m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom w) (m'.cart.1.lift_snd _ _ _)
  have hψ₁ : ψ₁.left ≫ m'.φ = m.φ ≫ ψ.left := m'.cart.1.lift_fst _ _ _
  have ext' : ∀ {T : Over S'} (x y : T ⟶ o₁'.A), x.left ≫ m'.φ = y.left ≫ m'.φ → x = y := fun x y e =>
    Over.OverMorphism.ext (m'.cart.1.hom_ext e (by rw [Over.w, Over.w]))

  have pa : ∀ {T : Over S'} (x : T ⟶ o₁.A), pushPt m'.cart.1.w (x ≫ ψ₁) = pushPt m.cart.1.w x ≫ ψ := fun x =>
    Over.OverMorphism.ext (by
      show (x ≫ ψ₁).left ≫ m'.φ = (x.left ≫ m.φ) ≫ ψ.left
      rw [Over.comp_left, Category.assoc, hψ₁, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ o₁.A),
      pushPt m.cart.1.w (x * y) = pushPt m.cart.1.w x * pushPt m.cart.1.w y := fun x y => map_mul (pushHom m.cart _) x y
  have pm' : ∀ {T : Over S'} (x y : T ⟶ o₁'.A),
      pushPt m'.cart.1.w (x * y) = pushPt m'.cart.1.w x * pushPt m'.cart.1.w y := fun x y => map_mul (pushHom m'.cart _) x y
  have inj' : ∀ {T : Over S'} {x y : T ⟶ o₁'.A}, pushPt m'.cart.1.w x = pushPt m'.cart.1.w y → x = y := fun e =>
    ext' _ _ (congrArg (fun z => z.left) e)
  haveI := hmon
  have hmon₁ : IsMonHom ψ₁ := by
    refine isMonHom_of_mul ψ₁ fun T x y => ?_
    apply inj'
    rw [pa, pm, MonObj.mul_comp, ← pa, ← pa, pm']

  have tc : ∀ z, (transl (o₁.eta z)).left ≫ m.φ = m.φ ≫ (transl (o.eta z)).left := by
    intro z
    have hu : pushPt m.cart.1.w (toUnit o₁.A ≫ o₁.eta z) = toUnit _ ≫ o.eta z := Over.OverMorphism.ext (by
      show (toUnit o₁.A ≫ o₁.eta z).left ≫ m.φ = (toUnit (Over.mk (o₁.A.hom ≫ f)) ≫ o.eta z).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, m.eta]
      simp)
    have e : pushPt m.cart.1.w (transl (o₁.eta z)) = pushPt m.cart.1.w (𝟙 o₁.A) ≫ transl (o.eta z) := by
      show pushPt m.cart.1.w (𝟙 o₁.A * (toUnit o₁.A ≫ o₁.eta z)) =
        pushPt m.cart.1.w (𝟙 o₁.A) ≫ (𝟙 o.A * (toUnit o.A ≫ o.eta z))
      rw [pm, hu, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (_ ≫ toUnit o.A) (toUnit _)]
    have e' : (transl (o₁.eta z)).left ≫ m.φ = ((𝟙 o₁.A : o₁.A ⟶ o₁.A).left ≫ m.φ) ≫ (transl (o.eta z)).left :=
      congrArg (fun z => z.left) e
    rw [e', Over.id_left, Category.id_comp]
  have hp : IsPullback m.φ ψ₁.left ψ.left m'.φ := by
    refine IsPullback.of_bot ?_ hψ₁.symm m'.cart.1
    rw [Over.w ψ₁, Over.w ψ]; exact m.cart.1
  refine ⟨ψ₁, hmon₁, fun c' => ?_, fun x => ?_, ?_, ?_, hdvd⟩
  · apply ext'
    have h₀ := congrArg (fun z => m.φ ≫ z.left) (hlin c')
    simp only [Over.comp_left, Category.assoc] at h₀ ⊢
    rw [hψ₁, m'.act, reassoc_of% hψ₁, reassoc_of% (m.act c')]
    exact h₀
  · apply ext'
    rw [m'.eta, heta]
    simp only [Over.comp_left, Category.assoc]
    rw [hψ₁, reassoc_of% (m.eta (g x))]
  · refine isGaloisCover_of_isPullback hgal hp ?_ (fun a c => ?_) (fun a c e => Subtype.ext (transl_injective e))
      (fun a => ?_) (fun a => ?_) (fun a => ?_)
    · show (transl 1).left = _
      rw [transl_one, Over.id_left]
    · show (transl (a.1 * c.1)).left = _
      rw [transl_mul, Over.comp_left]
    · obtain ⟨h, x, rfl⟩ := a
      have hi : (transl (o.eta (N • g x))).left ≫ ψ.left = ψ.left := hgal.inv ⟨_, mem_heckeSub o g N x⟩
      show (transl (o₁.eta (N • g x))).left ≫ ψ₁.left = ψ₁.left
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, hψ₁, ← Category.assoc, tc, Category.assoc, hi]
      · rw [Category.assoc, Over.w ψ₁, Over.w]
    · obtain ⟨h, x, rfl⟩ := a
      exact ⟨⟨_, mem_heckeSub o g N x⟩, tc _⟩
    · obtain ⟨h, x, rfl⟩ := a
      exact ⟨⟨_, mem_heckeSub o₁ g N x⟩, tc _⟩
  · have hs1 : m.φ₂ ≫ (fst o.A o.A).left = (fst o₁.A o₁.A).left ≫ m.φ := m.sq.1
    have hs2 : m.φ₂ ≫ (snd o.A o.A).left = (snd o₁.A o₁.A).left ≫ m.φ := m.sq.2
    have hn₀ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
    have hn₁ : (GlobalTheory.UPel.HT.Hecke.lbPow o₁.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hsq : sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply grpScheme_square_hom_ext
      · rw [Category.assoc, m'.sq.1, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, Category.assoc, hψ₁, Category.assoc, grpSchemeSquareProductMap_comp_fst,
          ← Category.assoc m.φ₂, hs1, Category.assoc]
      · rw [Category.assoc, m'.sq.2, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, Category.assoc, hψ₁, Category.assoc, grpSchemeSquareProductMap_comp_snd,
          ← Category.assoc m.φ₂, hs2, Category.assoc]
    have c₁ : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) :=
      (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
    have c₁' : GlobalTheory.CechPic.cls o₁'.P o₁'.isLB = GlobalTheory.CechPic.pull m'.φ₂ (GlobalTheory.CechPic.cls o'.P o'.isLB) :=
      (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have c₀ : GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls o'.P o'.isLB) = (k ^ 2 / c) • GlobalTheory.CechPic.cls o.P o.isLB := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB _ (pull_isLB o'.isLB _),
        ← (GlobalTheory.CechPic.cls_eq_iff hn₀ (pull_isLB o'.isLB _)).2 hP, cls_heckePow o.isLB]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hn₁ (pull_isLB o₁'.isLB _)).1 ?_⟩
    rw [cls_heckePow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB, c₁, c₁', ← GlobalTheory.CechPic.pull_comp, hsq,
      GlobalTheory.CechPic.pull_comp, c₀, map_nsmul]

end GlobalTheory.UPel.HT.Hecke.PullHecke
end
end
