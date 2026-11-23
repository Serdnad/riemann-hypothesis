module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle130
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.WedgeField

theorem exists_finite_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s]
    [CompactSpace X] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _) U le_top W le_top hU hW
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := fun x _ => by
    have hx : x ∈ (⨆ U : X.affineOpens, U.1 : X.Opens) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) hcov
  let A : Set X.Opens := (fun U : X.affineOpens => U.1) '' (t : Set X.affineOpens)
  have hfin : (infClosure A).Finite := (t.finite_toSet.image _).infClosure
  have haff : infClosure A ⊆ {V : X.Opens | IsAffineOpen V} :=
    infClosure_min (by rintro _ ⟨U, _, rfl⟩; exact U.2) fun a ha b hb => hinter a b ha hb
  letI inst : SemilatticeInf (infClosure A) :=
    Subtype.semilatticeInf fun x y hx hy => infClosed_infClosure hx hy
  refine ⟨infClosure A, inst, hfin.to_subtype, ⟨⟨fun p => ⟨p.1, haff p.2⟩, fun a b => rfl, ?_⟩⟩⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨⟨U.1, subset_infClosure ⟨U, hU, rfl⟩⟩, hx⟩

def sqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem sqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    sqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem wedge_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) (h2 : Function.Bijective m.pull2) (h : Wedge F') : Wedge F := by
  obtain ⟨e, he⟩ := h
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  let E2 : H2 F ≃ₗ[R] H2 F' := LinearEquiv.ofBijective m.pull2 h2
  refine ⟨(sqEquiv E1).trans (e.trans E2.symm), fun a b => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, sqEquiv_ιMulti, he, LinearEquiv.symm_apply_eq]
  exact (m.pullCohomologyTwo_cup a b).symm

theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

end GlobalTheory.CompanionTheory.Hodge.WedgeField
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows

namespace GlobalTheory.CompanionTheory.Dict

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def L0 : Cn F 0 →ₗ[R] C0 F where
  toFun f T := f (mk₀ T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L1 : Cn F 1 →ₗ[R] C1 F where
  toFun f _ _ φ := f (mk₁ φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L2 : Cn F 2 →ₗ[R] C2 F where
  toFun f _ _ _ φ ψ := f (mk₂ φ ψ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L3 : Cn F 3 →ₗ[R] C3 F where
  toFun f _ _ _ _ φ ψ χ := f (mk₃ φ ψ χ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem L0_bijective_cochain : Function.Bijective (L0 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj (Fin.last 0)), rfl⟩⟩
  obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective c
  exact congr_fun h X

theorem L1_bijective_cochain : Function.Bijective (L1 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj (Fin.last 1))
    (c.map (homOfLE (Fin.zero_le _))), rfl⟩⟩
  obtain ⟨X₀, X₁, φ, rfl⟩ := ComposableArrows.mk₁_surjective c
  exact congr_fun (congr_fun (congr_fun h X₀) X₁) φ

theorem L2_bijective_cochain : Function.Bijective (L2 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj (Fin.last 2))
    (c.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 3) ≤ Fin.last 2 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, φ, ψ, rfl⟩ := ComposableArrows.mk₂_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) φ) ψ

theorem L3_bijective_cochain : Function.Bijective (L3 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj 2)
    (c.obj (Fin.last 3)) (c.map (homOfLE (show (0 : Fin 4) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 4) ≤ 2 by decide)))
    (c.map (homOfLE (show (2 : Fin 4) ≤ Fin.last 3 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, X₃, φ, ψ, χ, rfl⟩ := ComposableArrows.mk₃_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) X₃) φ) ψ) χ

theorem cof_eq {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ C) (c' : Fin (n + 1) ⥤ C)
    (h : face i c = c') (u : c'.obj (Fin.last n) ⟶ c.obj (Fin.last (n + 1)))
    (hu : HEq (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) u) (f : Cn F n) :
    cof F n i f c = mp F u (f c') := by
  subst h
  obtain rfl := eq_of_heq hu
  rfl

theorem dn0 (f : Cn F 0) (c : Fin 2 ⥤ C) : dn F 0 f c = cof F 0 0 f c - cof F 0 1 f c := by
  simp [dn, Fin.sum_univ_two, sub_eq_add_neg]

theorem dn1 (f : Cn F 1) (c : Fin 3 ⥤ C) :
    dn F 1 f c = cof F 1 0 f c - cof F 1 1 f c + cof F 1 2 f c := by
  simp [dn, Fin.sum_univ_three, pow_succ, sub_eq_add_neg]

theorem dn2 (f : Cn F 2) (c : Fin 4 ⥤ C) :
    dn F 2 f c = cof F 2 0 f c - cof F 2 1 f c + cof F 2 2 f c - cof F 2 3 f c := by
  simp [dn, Fin.sum_univ_four, pow_succ, sub_eq_add_neg]

theorem eq_mk₁ (c : ComposableArrows C 1) (x : c.left ⟶ c.right) (h : c.hom = x) : c = mk₁ x := by
  obtain ⟨X₀, X₁, g, rfl⟩ := ComposableArrows.mk₁_surjective c
  subst h
  rfl

theorem eq_mk₂ (c : ComposableArrows C 2) (x : c.obj' 0 ⟶ c.obj' 1) (y : c.obj' 1 ⟶ c.obj' 2)
    (hx : map' c 0 1 = x) (hy : map' c 1 2 = y) : c = mk₂ x y := by
  obtain ⟨X₀, X₁, X₂, g₀, g₁, rfl⟩ := ComposableArrows.mk₂_surjective c
  subst hx hy
  rfl

section Faces

variable {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''')

theorem cech_nerve_face_one_zero : face 0 (mk₁ φ) = mk₀ T' := by
  exact ComposableArrows.ext₀ rfl
theorem cech_nerve_face_one_one : face 1 (mk₁ φ) = mk₀ T := by
  exact ComposableArrows.ext₀ rfl
theorem cech_nerve_face_two_zero : face 0 (mk₂ φ ψ) = mk₁ ψ := by
  exact eq_mk₁ (face 0 (mk₂ φ ψ)) ψ rfl
theorem cech_nerve_face_two_one : face 1 (mk₂ φ ψ) = mk₁ (φ ≫ ψ) := by
  exact eq_mk₁ (face 1 (mk₂ φ ψ)) (φ ≫ ψ) rfl
theorem cech_nerve_face_two_two : face 2 (mk₂ φ ψ) = mk₁ φ := by
  exact eq_mk₁ (face 2 (mk₂ φ ψ)) φ rfl
theorem face_zero_mk3 : face 0 (mk₃ φ ψ χ) = mk₂ ψ χ := by
  exact eq_mk₂ (face 0 (mk₃ φ ψ χ)) ψ χ rfl rfl
theorem face_one_mk3 : face 1 (mk₃ φ ψ χ) = mk₂ (φ ≫ ψ) χ := by
  exact eq_mk₂ (face 1 (mk₃ φ ψ χ)) (φ ≫ ψ) χ rfl rfl
theorem face_two_mk3 : face 2 (mk₃ φ ψ χ) = mk₂ φ (ψ ≫ χ) := by
  exact eq_mk₂ (face 2 (mk₃ φ ψ χ)) φ (ψ ≫ χ) rfl rfl
theorem face_three_mk3 : face 3 (mk₃ φ ψ χ) = mk₂ φ ψ := by
  exact eq_mk₂ (face 3 (mk₃ φ ψ χ)) φ ψ rfl rfl

end Faces

private theorem mp_id_apply (X : C) (x : F.obj X) : mp F (𝟙 X) x = x := by
  rw [mp, CategoryTheory.Functor.map_id]
  rfl

theorem L1_dn_zero_eq_d0_L0 (f : Cn F 0) : L1 F (dn F 0 f) = d0 F (L0 F f) := by
  funext T T' φ
  show dn F 0 f (mk₁ φ) = L0 F f T' - mp F φ (L0 F f T)
  rw [dn0, cof_eq F (n := 0) 0 (mk₁ φ) (mk₀ T') (cech_nerve_face_one_zero φ) (𝟙 T') HEq.rfl f,
    cof_eq F (n := 0) 1 (mk₁ φ) (mk₀ T) (cech_nerve_face_one_one φ) φ HEq.rfl f]
  show mp F (𝟙 T') (f (mk₀ T')) - mp F φ (f (mk₀ T)) = _
  rw [mp_id_apply F T' (f (mk₀ T'))]
  rfl

theorem L2_dn_one_eq_d1_L1 (f : Cn F 1) : L2 F (dn F 1 f) = d1 F (L1 F f) := by
  funext T T' T'' φ ψ
  show dn F 1 f (mk₂ φ ψ) = mp F ψ (L1 F f T T' φ) - L1 F f T T'' (φ ≫ ψ) + L1 F f T' T'' ψ
  rw [dn1, cof_eq F (n := 1) 0 (mk₂ φ ψ) (mk₁ ψ) (cech_nerve_face_two_zero φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 1 (mk₂ φ ψ) (mk₁ (φ ≫ ψ)) (cech_nerve_face_two_one φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 2 (mk₂ φ ψ) (mk₁ φ) (cech_nerve_face_two_two φ ψ) ψ HEq.rfl f]
  conv_lhs => rw [sub_add_comm]
  show mp F ψ (f (mk₁ φ)) - mp F (𝟙 T'') (f (mk₁ (φ ≫ ψ))) + mp F (𝟙 T'') (f (mk₁ ψ)) = _
  rw [mp_id_apply F T'' (f (mk₁ (φ ≫ ψ))), mp_id_apply F T'' (f (mk₁ ψ))]
  rfl

theorem L3_dn_two_eq_d2_L2 (f : Cn F 2) : L3 F (dn F 2 f) = d2 F (L2 F f) := by
  funext T T' T'' T''' φ ψ χ
  show dn F 2 f (mk₃ φ ψ χ) = L2 F f T' T'' T''' ψ χ - L2 F f T T'' T''' (φ ≫ ψ) χ +
    L2 F f T T' T''' φ (ψ ≫ χ) - mp F χ (L2 F f T T' T'' φ ψ)
  rw [dn2, cof_eq F (n := 2) 0 (mk₃ φ ψ χ) (mk₂ ψ χ) (face_zero_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 1 (mk₃ φ ψ χ) (mk₂ (φ ≫ ψ) χ) (face_one_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 2 (mk₃ φ ψ χ) (mk₂ φ (ψ ≫ χ)) (face_two_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 3 (mk₃ φ ψ χ) (mk₂ φ ψ) (face_three_mk3 φ ψ χ) χ HEq.rfl f]
  show mp F (𝟙 T''') (f (mk₂ ψ χ)) - mp F (𝟙 T''') (f (mk₂ (φ ≫ ψ) χ)) +
    mp F (𝟙 T''') (f (mk₂ φ (ψ ≫ χ))) - mp F χ (f (mk₂ φ ψ)) = _
  rw [mp_id_apply F T''' (f (mk₂ ψ χ)), mp_id_apply F T''' (f (mk₂ (φ ≫ ψ) χ)),
    mp_id_apply F T''' (f (mk₂ φ (ψ ≫ χ)))]
  rfl

theorem dictSt : DictSt := by
  intro R _ C _ F
  refine ⟨LinearEquiv.ofBijective (L0 F) (L0_bijective_cochain F), LinearEquiv.ofBijective (L1 F) (L1_bijective_cochain F),
    LinearEquiv.ofBijective (L2 F) (L2_bijective_cochain F), LinearEquiv.ofBijective (L3 F) (L3_bijective_cochain F),
    fun _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_,
    fun f => ?_, fun f => ?_, fun f => ?_⟩ <;> simp only [LinearEquiv.ofBijective_apply]
  · rfl
  · rfl
  · rfl
  · rfl
  · exact L1_dn_zero_eq_d0_L0 F f
  · exact L2_dn_one_eq_d1_L1 F f
  · exact L3_dn_two_eq_d2_L2 F f

end GlobalTheory.CompanionTheory.Dict
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.QCalc

section Linear

variable {R A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type} [CommRing R]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  [Module R B₀] [Module R B₁] [Module R B₂]
  [Module R C₀] [Module R C₁] [Module R C₂]
  {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂}
  {c₀ : C₀ →ₗ[R] C₁} {c₁ : C₁ →ₗ[R] C₂}
  {f₀ : A₀ →ₗ[R] B₀} {f₁ : A₁ →ₗ[R] B₁} {f₂ : A₂ →ₗ[R] B₂}
  {g₀ : B₀ →ₗ[R] C₀} {g₁ : B₁ →ₗ[R] C₁} {g₂ : B₂ →ₗ[R] C₂} {k : A₁ →ₗ[R] C₁}

theorem qIsoAt_comp (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x)) (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hk : ∀ x, k x = g₁ (f₁ x)) (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) :
    QIsoAt a₀ a₁ c₀ c₁ k := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · have hc : b₁ (f₁ x) = 0 := by rw [← hf₂, hx, map_zero]
    exact hf.1 x hx (hg.1 (f₁ x) hc ⟨y, by rw [hy, hk]⟩)
  · obtain ⟨w, y, hw, hy⟩ := hg.2 z hz
    obtain ⟨x, y', hx, hy'⟩ := hf.2 w hw
    refine ⟨x, y + g₀ y', hx, ?_⟩
    have e : f₁ x = w + b₀ y' := by rw [← hy']; abel
    rw [hk, e, map_add (f := _), hg₀, map_add (f := _), ← hy]
    abel

theorem qIsoAt_right (hf₀ : ∀ x, f₁ (a₀ x) = b₀ (f₀ x)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hk : ∀ x, k x = g₁ (f₁ x))
    (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt b₀ b₁ c₀ c₁ g₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨u, v, hu, hv⟩ := hf.2 x hx
    have e : f₁ u = x + b₀ v := by rw [← hv]; abel
    obtain ⟨w, hw⟩ := hK.1 u hu ⟨y + g₀ v, by rw [hk, e, map_add (f := _), map_add (f := _), hg₀, hy]⟩
    refine ⟨f₀ w - v, ?_⟩
    rw [map_sub, ← hf₀, hw, e]
    abel
  · obtain ⟨x, y, hx, hy⟩ := hK.2 z hz
    refine ⟨f₁ x, y, by rw [← hf₂, hx, map_zero], ?_⟩
    rw [← hk]
    exact hy

theorem qIsoAt_left (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hg₂ : ∀ x, g₂ (b₁ x) = c₁ (g₁ x))
    (hk : ∀ x, k x = g₁ (f₁ x))
    (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt a₀ a₁ b₀ b₁ f₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · exact hK.1 x hx ⟨g₀ y, by rw [← hg₀, hy, hk]⟩
  · have hc : c₁ (g₁ z) = 0 := by rw [← hg₂, hz, map_zero]
    obtain ⟨x, y, hx, hy⟩ := hK.2 (g₁ z) hc
    have hd : b₁ (f₁ x - z) = 0 := by rw [map_sub, ← hf₂, hx, hz, map_zero, sub_zero]
    obtain ⟨y', hy'⟩ := hg.1 (f₁ x - z) hd ⟨y, by rw [map_sub, ← hk, hy]⟩
    exact ⟨x, y', hx, hy'.symm⟩

end Linear

theorem qCalcSt : CxSt → QCalcSt := by
  intro hCx R _ C _ F D E _ _ G H m n k hk
  have cm : ∀ i x, pulln m (i + 1) (dn F i x) = dn G i (pulln m i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R C F).2 D G m i) x
  have cn : ∀ i x, pulln n (i + 1) (dn G i x) = dn H i (pulln n i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R D G).2 E H n i) x
  have zf : ∀ x : R, pulln m 0 ((0 : R →ₗ[R] Cn F 0) x) =
      (0 : R →ₗ[R] Cn G 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  have zg : ∀ x : R, pulln n 0 ((0 : R →ₗ[R] Cn G 0) x) =
      (0 : R →ₗ[R] Cn H 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  refine ⟨fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · exact qIsoAt_comp (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_comp (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_right zf (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_right (cm i) (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_left (cm 0) zg (cn 0) (hk 0) h₁.1 h₂.1
  · exact qIsoAt_left (cm (i + 1)) (cn i) (cn (i + 1)) (hk (i + 1)) (h₁.2 i) (h₂.2 i)

end GlobalTheory.CompanionTheory.QCalc
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

theorem existsUnique_const_of_trivSqZeroExt (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (bc : BC F F') :
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  intro hS z hz
  choose e he using bc.bij
  have hpure : ∀ (T : C) (r : TrivSqZeroExt R M) (b : F.obj T), e T (r ⊗ₜ[R] b) = r • bc.α T b := by
    intro T r b
    have h : (r ⊗ₜ[R] b : TrivSqZeroExt R M ⊗[R] F.obj T) = r • ((1 : TrivSqZeroExt R M) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h, map_smul, he]
  have hnat : ∀ {T T' : C} (φ : T ⟶ T') (x : TrivSqZeroExt R M ⊗[R] F.obj T),
      e T' ((mp F φ).toLinearMap.lTensor _ x) = mp F' φ (e T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
      rw [LinearMap.lTensor_tmul, hpure, hpure, map_smul]
      exact congrArg (r • ·) (bc.naturality φ b)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  let jj : ∀ T : C, M ⊗[R] F.obj T →ₗ[R] TrivSqZeroExt R M ⊗[R] F.obj T :=
    fun T ↦ (TrivSqZeroExt.inrHom R M).rTensor _
  have hsnd : ∀ (T : C) (x : M ⊗[R] F.obj T),
      (TrivSqZeroExt.sndHom R M).rTensor _ (jj T x) = x := by
    intro T x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcomm : ∀ {T T' : C} (φ : T ⟶ T') (x : M ⊗[R] F.obj T),
      jj T' ((mp F φ).toLinearMap.lTensor M x) = (mp F φ).toLinearMap.lTensor _ (jj T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  have hconst : ∀ (T : C) (r : TrivSqZeroExt R M),
      algebraMap (TrivSqZeroExt R M) (F'.obj T) r = e T (r ⊗ₜ[R] (1 : F.obj T)) := by
    intro T r
    rw [hpure, map_one, Algebra.algebraMap_eq_smul_one]
  let w : C0 F' := fun T ↦ e T (jj T (z T))
  have hw : d0 F' w = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [w, Pi.zero_apply]
    rw [← hnat, ← hcomm, ← hz, sub_self]
  obtain ⟨r, hr⟩ := (hS.1 w).1 hw
  have hjjr : ∀ T : C, jj T (z T) = r ⊗ₜ[R] (1 : F.obj T) := by
    intro T
    apply (e T).injective
    rw [← hconst]
    exact (congrFun hr T).symm
  refine ⟨r.snd, fun T ↦ ?_, fun m₂ hm₂ ↦ ?_⟩
  · rw [← hsnd T (z T), hjjr T]
    simp
  · have h0 : algebraMap (TrivSqZeroExt R M) (C0 F') (TrivSqZeroExt.inr (m₂ - r.snd)) = 0 := by
      funext T
      have hd : (m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have h1 : z T = r.snd ⊗ₜ[R] (1 : F.obj T) := by
          rw [← hsnd T (z T), hjjr T]
          simp
        rw [TensorProduct.sub_tmul, ← hm₂ T, ← h1, sub_self]
      have h2 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have : jj T ((m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T)) =
            (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) := by
          simp [jj]
        rw [← this, hd, map_zero]
      change algebraMap (TrivSqZeroExt R M) (F'.obj T) _ = 0
      rw [hconst, h2, map_zero]
    have h3 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) = 0 :=
      hS.2 (h0.trans (map_zero _).symm)
    have h4 := congrArg TrivSqZeroExt.snd h3
    simpa [sub_eq_zero] using h4

end GlobalTheory.CompanionTheory.Axis
end
end

section

theorem _root_.GlobalTheory.T.finite_subquotients :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (ι : Type) [Fintype ι] [DecidableEq ι], PositivityTheory.Rg.BcN.F2.FinSubq F ι :=
  GlobalTheory.CompanionTheory.RepFinSubq.finSubq
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

theorem _root_.GlobalTheory.T.hecke_algebra_structure : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | exact GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | (intros; apply GlobalTheory.CompanionTheory.HeckeAlg.hk_alg <;> assumption)
end
