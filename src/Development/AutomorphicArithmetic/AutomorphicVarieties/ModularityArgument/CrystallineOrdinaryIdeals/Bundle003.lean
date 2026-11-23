module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CrLocal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem qcont_map {X V W : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W]
    [Module ℚ_[l] W] (f : V →ₗ[ℚ_[l]] W) {c : X → V} (hc : QCont l c) : QCont l fun x => f (c x) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : ContinuousAdd W := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap f).comp hc

theorem qcont_add {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c d : X → V}
    (hc : QCont l c) (hd : QCont l d) : QCont l fun x => c x + d x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hc hd

theorem qcont_sum {X V ι : Type} [Fintype ι] [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c : ι → X → V}
    (hc : ∀ i, QCont l (c i)) : QCont l fun x => ∑ i, c i x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact continuous_finsetSum _ fun i _ => hc i

theorem contAction_of_qcont {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V)
    (h : ∀ v, QCont l fun g => ρ g v) : ContAction ρ := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  have h' : ∀ v, Continuous fun g => ρ g v := fun v => by
    have := h v
    unfold QCont at this
    rwa [← eq_moduleTopology ℚ_[l] V] at this
  let b := Module.finBasis ℚ_[l] V
  have e : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.coord i p.2 • ρ p.1 (b i) := by
    funext p

    conv_lhs => rw [← b.sum_repr p.2, map_sum]
    simp only [map_smul, Basis.coord_apply]
  unfold ReciprocityTheory.Gal.ContAction
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((IsModuleTopology.continuous_of_linearMap (b.coord i)).comp continuous_snd).smul ((h' _).comp continuous_fst)

theorem qcont_colRep {B : Type} [CommRing B] [Algebra ℚ_[l] B] (ρ : G →* GL (Fin 3) B)
    (h : ∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) (v : Fin 3 → B) :
    QCont l fun g => resCoef ℚ_[l] (colRep ρ) g v := by
  have e : (fun g => resCoef ℚ_[l] (colRep ρ) g v) = fun g => ∑ i, ∑ j,
      ((LinearMap.single ℚ_[l] (fun _ : Fin 3 => B) i).comp (LinearMap.mulRight ℚ_[l] (v j)))
        ((ρ g : Matrix (Fin 3) (Fin 3) B) i j) := by
    funext g
    ext k
    change (ρ g : Matrix (Fin 3) (Fin 3) B).mulVec v k = _
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact qcont_sum fun i => qcont_sum fun j => qcont_map _ (h i j)

variable [IsTopologicalGroup G] {φ : G →* GQ l}

theorem cr_sub (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (f : V →ₗ[ℚ_[l]] W) (hf : ∀ g x, f (ρ g x) = σ g (f x)) (hi : Function.Injective f) (h : IsCr φ σ) :
    IsCr φ ρ := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact ((isCrys_isDR_sub_quot φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ) f hf).1 hi).1 h

theorem cr_prod (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (h : IsCr φ ρ) (h' : IsCr φ σ) : IsCr φ (ρ.prod σ) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact (isCrys_isDR_prod φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ)).1 h h'

theorem exists_cr_of_finset (hφ : IsOpenEmbedding φ) {V ι : Type} [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (N : ι → Set V)
    (h : ∀ i, ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → x ∈ N i) (S : Finset ι) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → ∀ i ∈ S, x ∈ N i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, 0, fun v => ?_, ?_,
      fun _ _ => Subsingleton.elim _ _, by simp⟩
    · exact @continuous_const _ _ _ (moduleTopology ℚ_[l] PUnit) v
    · unfold IsCr
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, mul_zero]
  | insert a S _ ih =>
    obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := ih
    obtain ⟨W', _, _, _, σ', f', h1', h2', h3', h4'⟩ := h a
    refine ⟨W × W', inferInstance, inferInstance, inferInstance, σ.prod σ', f.prod f', fun v => ?_,
      cr_prod hφ σ σ' h1 h1' h2 h2', fun g x => ?_, fun x hx i hi => ?_⟩
    · have := qcont_add (qcont_map (LinearMap.inl ℚ_[l] W W') (h1 v.1)) (qcont_map (LinearMap.inr ℚ_[l] W W') (h1' v.2))
      convert this using 2 with g
      ext <;> simp [Representation.prod]
    · ext <;> simp [Representation.prod, h3, h3']
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h4' x (congrArg Prod.snd hx)
      · exact h4 x (congrArg Prod.fst hx) i hi

theorem isCr_of_local : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (ρ : G →* GL (Fin 3) B), (∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) → (∀ (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra B B'] [IsScalarTower ℚ_[l] B B'], IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (algebraMap B B')).comp ρ))) → IsCr φ (colRep ρ) := by
  intro l _ G _ _ _ φ hφ B _ _ _ ρ hc h
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := exists_cr_of_finset hφ (resCoef ℚ_[l] (colRep ρ))
    (fun m : MaximalSpectrum B => {v | ∀ i, algebraMap B (Localization.AtPrime m.asIdeal) (v i) = 0})
    (fun m => by
      let a : B →ₗ[ℚ_[l]] Localization.AtPrime m.asIdeal :=
        (IsScalarTower.toAlgHom ℚ_[l] B (Localization.AtPrime m.asIdeal)).toLinearMap
      haveI : Module.Finite ℚ_[l] (Localization.AtPrime m.asIdeal) :=
        Module.Finite.of_surjective a (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
      refine ⟨Fin 3 → Localization.AtPrime m.asIdeal, inferInstance, inferInstance, inferInstance,
        resCoef ℚ_[l] (colRep ((Matrix.GeneralLinearGroup.map
          (algebraMap B (Localization.AtPrime m.asIdeal))).comp ρ)), a.compLeft (Fin 3),
        qcont_colRep _ fun i j => qcont_map a (hc i j), h _, fun g x => ?_, fun x hx i => congrFun hx i⟩
      ext k
      exact RingHom.map_mulVec (algebraMap B (Localization.AtPrime m.asIdeal)) _ x k) Finset.univ
  refine cr_sub hφ (resCoef ℚ_[l] (colRep ρ)) σ (qcont_colRep ρ hc) h1 f h3 ?_ h2
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  exact eq_zero_of_localization _ fun J hJ => h4 x hx ⟨J, hJ⟩ (Finset.mem_univ _) i

end GlobalTheory.CrLocal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.LCrConj

open TensorProduct

private theorem isCr_transfer {l : ℕ} [Fact l.Prime] {G A A' V V' : Type} [Group G] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [CommRing A']
    [Algebra ℚ_[l] A'] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V']
    (φ : G →* GQ l) (ρ : Representation A G V)
    (ρ' : Representation A' G V') (f : V ≃ₗ[ℚ_[l]] V') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    IsCr φ ρ ↔ IsCr φ ρ' := by
  let F : V ⊗[ℚ_[l]] Bcr l ≃ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bcr l := TensorProduct.congr f (LinearEquiv.refl _ _)
  have hF : ∀ g x, F (actC φ (resCoef ℚ_[l] ρ) g x) = actC φ (resCoef ℚ_[l] ρ') g (F x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b => simp [F, actC, resCoef, hf]
  have hD : (Dcr φ (resCoef ℚ_[l] ρ)).map F.toLinearMap = Dcr φ (resCoef ℚ_[l] ρ') := by
    ext x
    obtain ⟨x, rfl⟩ := F.surjective x
    rw [Submodule.mem_map_equiv, F.symm_apply_apply]
    simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      ← hF, F.injective.eq_iff]
  unfold IsCr
  rw [← hD, LinearEquiv.finrank_map_eq, f.finrank_eq]

private theorem isCr_conjGL {l : ℕ} [Fact l.Prime] {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}
    (φ : G →* GQ l) (r : G →* GL (Fin n) A) (h : GL (Fin n) A) :
    IsCr φ (colRep r) ↔ IsCr φ (colRep (conjGL h r)) :=
  isCr_transfer φ (colRep r) (colRep (conjGL h r))
    ((Matrix.toLinearEquiv' (h : Matrix (Fin n) (Fin n) A) h.invertible).restrictScalars ℚ_[l]) fun g x => by
      simp [colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]

private def glPart {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G)
    (r : G →* GG (m := m) (R := R))
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem isLCr_iff' {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]
    (r : GQ l →* GG (m := 3) (R := B))
    (h : ∀ g ∈ D.HL, (r g).right = 1) : D.IsLCr r ↔ IsCr D.HL.subtype (colRep (glPart D.HL r h)) := by
  refine ⟨fun ⟨ρ, h1, h2⟩ => ?_, fun h2 => ⟨_, fun _ => rfl, h2⟩⟩
  have : ρ = glPart D.HL r h := MonoidHom.ext h1
  exact this ▸ h2

end GlobalTheory.LCrConj


open GlobalTheory.LCrConj in
theorem GlobalTheory.LCrConj.main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG (m := 3) (R := B)) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _ _ r h hm _ hc
  have h1 : ∀ g ∈ D.HL, (r g).right = 1 := fun g hg => (hm g).trans hg.1
  have hm' : HasMult D.η (conjBy h r) := fun g => (by simp [conjBy] : (conjBy h r g).right = (r g).right).trans (hm g)
  have h1' : ∀ g ∈ D.HL, (conjBy h r g).right = 1 := fun g hg => (hm' g).trans hg.1
  have he : glPart D.HL (conjBy h r) h1' = conjGL h (glPart D.HL r h1) := by
    ext g : 1
    have h2 : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by rw [map_inv]; rfl
    show (conjBy h r g).left = _
    rw [h2, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, h1 g g.2, mul_one, sgnAct_one,
      sgnAct_one]
    rfl
  rw [isLCr_iff' D r h1, isCr_conjGL _ _ h, ← he, ← isLCr_iff']
  exact hc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem exists_character_filtration_of_sub_smul_mem {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (ρ : Representation E G V) (S : Set (G →* Eˣ)) (F' F'' : Submodule E V)
    (hQ : ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ∧ ∀ i < n, F i ≤ F (i + 1) ∧
      ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i)
    (hle : F' ≤ F'') (κ : G →* Eˣ) (hκ : κ ∈ S)
    (h : ∀ y ∈ F'', ∀ g : G, (ρ g) y - ((κ g : Eˣ) : E) • y ∈ F') :
    ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F'' ∧ ∀ i < n, F i ≤ F (i + 1) ∧
      ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
  classical
  have step : ∀ W : Submodule E V, F' ≤ W →
      (∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ∧ ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i) →
      ∀ v ∈ F'', ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ⊔ E ∙ v ∧
        ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
    rintro W hW ⟨n, F, h0, hn, hs⟩ v hv
    refine ⟨n + 1, fun i => if i = n + 1 then W ⊔ E ∙ v else F i, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      by_cases hin : i < n
      · have h1 : i ≠ n + 1 := by omega
        have h2 : i + 1 ≠ n + 1 := by omega
        simp only [h1, h2, if_false]
        exact hs i hin
      · have hi' : i = n := by omega
        subst hi'
        have h1 : i ≠ i + 1 := by omega
        simp only [h1, if_true, if_false, hn]
        exact ⟨le_sup_left, κ, hκ, v, rfl, fun g => hW (h v hv g)⟩
  have key : ∀ s : Finset V, (↑s : Set V) ⊆ F'' →
      ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ⊔ Submodule.span E (↑s : Set V) ∧
        ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using hQ
    · intro a s _ ih hs
      rw [Finset.coe_insert] at hs ⊢
      have h1 := step (F' ⊔ Submodule.span E ↑s) le_sup_left
        (ih (fun z hz => hs (Set.mem_insert_of_mem a hz))) a (hs (Set.mem_insert a _))
      rw [Submodule.span_insert, sup_comm (E ∙ a), ← sup_assoc]
      exact h1
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian F'' : F''.FG)
  obtain ⟨n, F, h0, hn, hst⟩ := key s (by rw [← hs]; exact Submodule.subset_span)
  refine ⟨n, F, h0, ?_, hst⟩
  rw [hn, hs, sup_eq_right.mpr hle]


theorem _root_.GlobalTheory.T.filtBy_positiveWeight_of_two_character_extension : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a b : G →* Bˣ), Continuous (fun g => (a g : B)) → Continuous (fun g => (b g : B)) → ∀ wa wb : ℤ, 1 ≤ wa → 1 ≤ wb → (∀ g, φ g ∈ Iq l → a g = cycA l l B (φ g) ^ wa) → (∀ g, φ g ∈ Iq l → b g = cycA l l B (φ g) ^ wb) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h), FiltBy (resCoef E (ext2 a b x hx)) {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ a b _ _ wa wb hwa hwb hIa hIb x hx
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  have hmemI : ∀ c : B, c - algebraMap E B (π c) ∈ RingHom.ker (π : B →+* E) := by
    intro c
    rw [RingHom.mem_ker]
    simp
  obtain ⟨M, hM⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro c hc
    exact mem_nilradical.mpr (hπ c (by simpa using hc))
  set I := RingHom.ker (π : B →+* E) with hIdef
  have hMz : ∀ c ∈ I ^ M, c = 0 := by
    intro c hc
    rw [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at hc
    exact hc
  have hstep : ∀ (c : B) (k : ℕ) (y : B), y ∈ I ^ k →
      c * y - algebraMap E B (π c) * y ∈ I ^ (k + 1) := by
    intro c k y hy
    rw [← sub_mul, pow_succ']
    exact Ideal.mul_mem_mul (hmemI c) hy
  have hcyc : ∀ σ, Units.map (π : B →* E) (cycA l l B σ) = cycA l l E σ := by
    intro σ
    ext
    simp only [cycA, Units.coe_map, MonoidHom.comp_apply, MonoidHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B, IsScalarTower.algebraMap_apply ℚ_[l] E B,
      AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E _).symm
  have hwt : ∀ (c : G →* Bˣ) (w : ℤ), (∀ g, φ g ∈ Iq l → c g = cycA l l B (φ g) ^ w) →
      HasWeight φ ((Units.map (π : B →* E)).comp c) w := by
    intro c w hc
    refine ⟨⊤, by simp, fun g _ hg => ?_⟩
    rw [MonoidHom.comp_apply, hc g hg, map_zpow, hcyc]
  have hsm : ∀ (u : Bˣ) (y : B × B), ((Units.map (π : B →* E) u : Eˣ) : E) • y =
      (algebraMap E B (π u) * y.1, algebraMap E B (π u) * y.2) := by
    intro u y
    ext <;> simp [Algebra.smul_def]
  unfold FiltBy
  set S : Set (G →* Eˣ) := {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} with hS
  have hSa : (Units.map (π : B →* E)).comp a ∈ S := ⟨wa, hwa, hwt a wa hIa⟩
  have hSb : (Units.map (π : B →* E)).comp b ∈ S := ⟨wb, hwb, hwt b wb hIb⟩
  set ρ := resCoef E (ext2 a b x hx) with hρdef
  have hρ : ∀ g (y : B × B), ρ g y = ((a g : B) * y.1 + x g * (b g : B) * y.2, (b g : B) * y.2) :=
    fun g y => rfl
  set P1 : ℕ → Submodule E (B × B) := fun k => ((I ^ k).restrictScalars E).prod ⊥ with hP1
  set P2 : ℕ → Submodule E (B × B) := fun k => (⊤ : Submodule E B).prod ((I ^ k).restrictScalars E)
    with hP2
  have mP1 : ∀ k z, z ∈ P1 k ↔ z.1 ∈ I ^ k ∧ z.2 = 0 := by
    intro k z
    simp [hP1, Submodule.mem_prod]
  have mP2 : ∀ k z, z ∈ P2 k ↔ z.2 ∈ I ^ k := by
    intro k z
    simp [hP2, Submodule.mem_prod]
  have Q0 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = ⊥ ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i :=
    ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hQ1 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P1 (M - j) ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    intro j
    induction j with
    | zero =>
      refine exists_character_filtration_of_sub_smul_mem ρ S ⊥ (P1 (M - 0)) Q0 bot_le _ hSa ?_
      intro y hy g
      rw [mP1, Nat.sub_zero] at hy
      have hy0 : y = 0 := Prod.ext (hMz _ hy.1) hy.2
      subst hy0
      simp
    | succ j ih =>
      by_cases hj : j < M
      · have e : M - j = (M - (j + 1)) + 1 := by omega
        rw [e] at ih
        refine exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSa ?_
        · intro z hz
          rw [mP1] at hz ⊢
          exact ⟨Ideal.pow_le_pow_right (Nat.le_succ _) hz.1, hz.2⟩
        · intro y hy g
          rw [mP1] at hy
          rw [mP1, MonoidHom.comp_apply, hsm, hρ]
          refine ⟨?_, by simp [hy.2]⟩
          simpa [hy.2] using hstep (a g : B) _ y.1 hy.1
      · have e : M - (j + 1) = M - j := by omega
        rw [e]
        exact ih
  have T12 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 M ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    have h1 := hQ1 M
    rw [Nat.sub_self] at h1
    refine exists_character_filtration_of_sub_smul_mem ρ S _ _ h1 ?_ _ hSa ?_
    · intro z hz
      rw [mP1] at hz
      rw [mP2, hz.2]
      exact zero_mem _
    · intro y hy g
      rw [mP2] at hy
      have hy2 := hMz _ hy
      rw [mP1, MonoidHom.comp_apply, hsm, hρ]
      exact ⟨by simp, by simp [hy2]⟩
  have hQ2 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 (M - j) ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    intro j
    induction j with
    | zero =>
      rw [Nat.sub_zero]
      exact T12
    | succ j ih =>
      by_cases hj : j < M
      · have e : M - j = (M - (j + 1)) + 1 := by omega
        rw [e] at ih
        refine exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSb ?_
        · intro z hz
          rw [mP2] at hz ⊢
          exact Ideal.pow_le_pow_right (Nat.le_succ _) hz
        · intro y hy g
          rw [mP2] at hy
          rw [mP2, MonoidHom.comp_apply, hsm, hρ]
          simpa using hstep (b g : B) _ y.2 hy
      · have e : M - (j + 1) = M - j := by omega
        rw [e]
        exact ih
  obtain ⟨n, F, h0, hn, hs⟩ := hQ2 M
  have htop : P2 (M - M) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [mP2, Nat.sub_self]
    simp
  exact ⟨n, F, h0, hn.trans htop, hs⟩
end
