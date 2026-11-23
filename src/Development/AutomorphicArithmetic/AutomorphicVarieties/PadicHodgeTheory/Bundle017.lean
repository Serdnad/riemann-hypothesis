module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem idx_GK {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (Om l)) :
    K.fixingSubgroup.index = finrank ℚ_[l] K :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (Om l) K).symm

private theorem sup_Iq {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    GK K ⊔ Iq l = (K0 K).fixingSubgroup := by
  haveI := K.2
  have ho : IsOpen ((GK K ⊔ Iq l : Subgroup (GQ l)) : Set (GQ l)) :=
    Subgroup.isOpen_mono le_sup_left (IntermediateField.fixingSubgroup_isOpen K.1)
  have hc := Subgroup.isClosed_of_isOpen _ ho
  have h1 := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ_[l]) (K := Om l) ⟨GK K ⊔ Iq l, hc⟩
  have h2 : IntermediateField.fixedField (GK K ⊔ Iq l) = K0 K := by
    apply le_antisymm
    · refine le_inf ?_ ?_
      · rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
        exact IntermediateField.fixedField_le le_sup_left
      · rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l)]
        exact IntermediateField.fixedField_le le_sup_right
    · rw [IntermediateField.le_iff_le]
      exact sup_le (IntermediateField.fixingSubgroup_le inf_le_left)
        (IntermediateField.fixingSubgroup_le inf_le_right)
  rw [← h2]
  exact h1.symm

theorem UpperTheory.V.Loc.isCrIff :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (ρ : Representation A ↥(GK K) V), (IsCr (GK K).subtype ρ ↔ Crys K ρ) ∧ (IsDr (GK K).subtype ρ ↔ DeRham K ρ) := by
  intro l _ K A _ _ V _ _ _ _ ρ
  have hC : Dcr (GK K).subtype (resCoef ℚ_[l] ρ) = Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
    unfold Dcr Dcris
    refine iInf_congr fun g => ?_
    have : actC (GK K).subtype (resCoef ℚ_[l] ρ) g = actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g := by
      unfold actC actVB
      congr 1
      ext b
      exact ((PP l).PD_actB K g b).symm
    rw [this]
  have hD : Ddr (GK K).subtype (resCoef ℚ_[l] ρ) = DdR ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
    unfold Ddr DdR
    refine iInf_congr fun g => ?_
    have : actD (GK K).subtype (resCoef ℚ_[l] ρ) g = actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g := by
      unfold actD actVdR
      congr 1
      ext b
      exact ((PP l).PD_actdR K g b).symm
    rw [this]
  constructor
  · unfold IsCr Crys IsCrys
    rw [hC, Subgroup.range_subtype, sup_Iq, idx_GK]
  · unfold IsDr DeRham IsDR
    rw [hD, Subgroup.range_subtype, show (GK K).index = finrank ℚ_[l] K.1 from idx_GK K.1]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc.BlochKatoDimension

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {K : FinExt l} (e : G ≃* ↥(GK K))
  {E : Type} [Field E] [Algebra ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] E V] (ρ : Representation E G V)

private def tr : Representation ℚ_[l] ↥(GK K) V := (resCoef ℚ_[l] ρ).comp e.symm.toMonoidHom

private theorem tr_apply (g : G) (v : V) : tr e ρ (e g) v = ρ g v := by
  simp [tr, resCoef]

private theorem actVB_tr (g : G) (x : V ⊗[ℚ_[l]] Bcr l) :
    actVB ((PP l).PD K) (tr e ρ) (e g) x = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, actC, tr_apply, (PP l).PD_actB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem actVdR_tr (g : G) (x : V ⊗[ℚ_[l]] Bdr l) :
    actVdR ((PP l).PD K) (tr e ρ) (e g) x = actD ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, actD, tr_apply, (PP l).PD_actdR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem actD_res (φ : G →* GQ l) (g : G) (x : V ⊗[ℚ_[l]] Bdr l) :
    actD φ (resCoef ℚ_[l] ρ) g x = actD φ ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actD, resCoef]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem Ddr_res (φ : G →* GQ l) :
    Ddr φ (resCoef ℚ_[l] ρ) = (Ddr φ ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [Ddr, sub_eq_zero, actD_res]

private theorem DdR_tr :
    DdR ((PP l).PD K) (tr e ρ) = (Ddr ((GK K).subtype.comp e.toMonoidHom) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp only [DdR, Ddr, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply]
  rw [e.surjective.forall]
  simp only [actVdR_tr]

private theorem h0V_tr_eq_restrictScalars_h0 : H0V (tr e ρ) = (H0 ρ).restrictScalars ℚ_[l] := by
  ext x
  simp only [H0V, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, H0, Representation.mem_invariants]
  rw [e.surjective.forall]
  simp only [tr_apply]

variable (K E V) in
private theorem FilV_eq (a : ℤ) :
    FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a =
      (UpperTheory.V.Loc.FilT (l := l) E V a).restrictScalars ℚ_[l] := by
  have hF : (((PP l).PD K).Fil a).restrictScalars ℚ_[l] =
      (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] :=
    SetLike.coe_injective ((PP l).PD_Fil K (botExt l) a)
  have h : ∀ (N : Submodule ℚ_[l] (Bdr l)) y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      N.subtype y = AlgebraTensorModule.map (LinearMap.id : V →ₗ[E] V) N.subtype y := by
    intro N y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  ext x
  rw [FilV, hF]
  simp only [UpperTheory.V.Loc.FilT, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
  [ContinuousConstSMul ℚ_[l] V]

private theorem mem_Z1f_transport_iff (he : Continuous e) (he' : Continuous e.symm) (c : ↥(GK K) → V) :
    c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ) ↔
      (c ∘ e) ∈ UpperTheory.V.Loc.finiteCocycles ((GK K).subtype.comp e.toMonoidHom) ρ := by
  show ((Continuous c ∧ ∀ g h, c (g * h) = c g + tr e ρ g (c h)) ∧
      ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actVB ((PP l).PD K) (tr e ρ) g x - x) ↔
    ((Continuous (c ∘ e) ∧ ∀ g h, c (e (g * h)) = c (e g) + ρ g (c (e h))) ∧
      ∃ x, ∀ g, c (e g) ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x - x)
  refine and_congr (and_congr ⟨fun h => h.comp he, fun h => ?_⟩ ?_) (exists_congr fun x => ?_)
  · simpa only [Function.comp_def, MulEquiv.apply_symm_apply] using h.comp he'
  · rw [e.surjective.forall₂]
    simp only [tr_apply, map_mul]
  · rw [e.surjective.forall]
    simp only [actVB_tr]

private def cocycleTransportToH1f (he : Continuous e) (he' : Continuous e.symm) :
    ↥(Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ)) →ₗ[ℚ_[l]] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) where
  toFun c := ⟨Submodule.Quotient.mk ⟨c.1 ∘ e, ((mem_Z1f_transport_iff e ρ he he' c.1).mp c.2).1⟩,
    ⟨_, (mem_Z1f_transport_iff e ρ he he' c.1).mp c.2, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem cocycle_transport_H1f_surjective (he : Continuous e) (he' : Continuous e.symm) :
    Function.Surjective (cocycleTransportToH1f e ρ he he') := by
  rintro ⟨_, c, hc, rfl⟩
  have h : (c.1 ∘ e.symm) ∘ e = c.1 := by
    funext g
    simp
  refine ⟨⟨c.1 ∘ e.symm, (mem_Z1f_transport_iff e ρ he he' _).mpr (by rw [h]; exact hc)⟩, Subtype.ext ?_⟩
  exact congrArg Submodule.Quotient.mk (Subtype.ext h)

private theorem ker_cocycle_transport_H1f (he : Continuous e) (he' : Continuous e.symm) :
    LinearMap.ker (cocycleTransportToH1f e ρ he he') =
      (Formalism.WeaklyAdmissibleFiltrations.B1 (tr e ρ)).comap (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ)).subtype := by
  ext c
  rw [LinearMap.mem_ker, Subtype.ext_iff]
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  refine (mem_coboundaries1 ρ (c.1 ∘ e)).trans ?_
  refine exists_congr fun m => ?_
  show (∀ g, c.1 (e g) = ρ g m - m) ↔ (fun g => tr e ρ g m - m) = c.1
  rw [funext_iff, e.surjective.forall]
  simp only [tr_apply]
  exact forall_congr' fun g => eq_comm

private def h1fEquiv (he : Continuous e) (he' : Continuous e.symm) :
    FiniteCohomology ((PP l).PD K) (tr e ρ) ≃ₗ[ℚ_[l]] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) :=
  (Submodule.quotEquivOfEq _ _ (ker_cocycle_transport_H1f e ρ he he').symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (cocycle_transport_H1f_surjective e ρ he he'))

end UpperTheory.V.Loc.BlochKatoDimension

open UpperTheory.V.Loc.BlochKatoDimension in
theorem UpperTheory.V.Loc.bkDim :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → IsDr φ ρ → Module.Finite E ↥(finiteCohomology φ ρ) ∧
      finrank E ↥(finiteCohomology φ ρ) + finrank E ↥(UpperTheory.V.Loc.FilD φ ρ 0) =
        finrank E ↥(H0 ρ) + φ.range.index * finrank E V := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ V _ _ _ _ _ _ _ _ _ ρ hc hdR
  obtain ⟨K, e, he, he', hφe, -, hind, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  rw [IsDr, hind, Ddr_res] at hdR
  rw [hind]
  clear hind hφ
  subst hφe
  have hD := (hP.bk l (PP l) (AIP l) T K).1
  have hcont : ∀ x, Continuous fun g => tr e ρ g x := fun x =>
    hc.comp (he'.prodMk continuous_const)
  have hdR' : IsDR ((PP l).PD K) (tr e ρ) := by
    rw [IsDR, DdR_tr]
    exact hdR
  obtain ⟨hfin, hdim⟩ := hD V (tr e ρ) hcont hdR'
  haveI : Module.Finite ℚ_[l] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) :=
    Module.Finite.equiv (h1fEquiv e ρ he he')
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, ?_⟩
  have hH1 : finrank ℚ_[l] (FiniteCohomology ((PP l).PD K) (tr e ρ)) =
      finrank ℚ_[l] E * finrank E ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) := by
    rw [(h1fEquiv e ρ he he').finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (tr e ρ)) = finrank ℚ_[l] E * finrank E ↥(H0 ρ) := by
    rw [h0V_tr_eq_restrictScalars_h0, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR ((PP l).PD K) (tr e ρ) ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 0) =
      finrank ℚ_[l] E * finrank E ↥(UpperTheory.V.Loc.FilD ((GK K).subtype.comp e.toMonoidHom) ρ 0) := by
    rw [DdR_tr, FilV_eq K E V, ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [IsDR, ← finrank_mul_finrank ℚ_[l] E V] at hdR'
  rw [hH1, hH0, hdR', hF] at hdim
  have hd : (finrank ℚ_[l] E : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := E)).ne'
  push_cast at hdim
  have : ((finrank E ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) +
      finrank E ↥(UpperTheory.V.Loc.FilD ((GK K).subtype.comp e.toMonoidHom) ρ 0) : ℕ) : ℤ) =
      ((finrank E ↥(H0 ρ) + finrank ℚ_[l] ↥K.1 * finrank E V : ℕ) : ℤ) := by
    push_cast
    refine mul_left_cancel₀ hd ?_
    linear_combination hdim
  exact_mod_cast this

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial
open GlobalTheory.UnramifiedCrys

private def algSub (p : ℕ) [hp : Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_pos hp.out.pos _).ne'⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  neg_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    have h := sub_pow_char_pow (p := p) (n := a) (0 : R) x
    rwa [zero_sub, hx, zero_pow (pow_pos hp.out.pos _).ne', zero_sub] at h

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        (M g).map (zlW p R) * W.map (WittVector.map f) = W :=
  _root_.UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg ρ hopen M hM hJ

theorem UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ_[l]), IsUnit C.det → ∃ N N' : Matrix (Fin n) (Fin n) (Bcr l), N * N' = 1 ∧ (∀ i j, (PP l).ιB (N i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ (∀ i j, (PP l).ιB (N' i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ N.map (PP l).φB = C.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l])) * N ∧ ∀ g ∈ Iq l, N.map ((PP l).actQ g) = N := by
  intro l _ n C hC
  obtain ⟨-, -, hI, ⟨σ, hσ⟩, -⟩ := iqBasic l
  obtain ⟨Ti⟩ := tiedP l
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det C).2 hC
  haveI : CompactSpace (Matrix (Fin n) (Fin n) ℤ_[l]) := inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[l]))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l]) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → ℤ_[l]))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℤ_[l])).symm.isEmbedding.isTotallyDisconnected_range.1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l])ˣ :=
    Units.isEmbedding_embedProduct.isTotallyDisconnected_range.1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨f, hf, hfI, hfσ⟩ := frobFree σ hσ (Matrix (Fin n) (Fin n) ℤ_[l])ˣ u⁻¹
  obtain ⟨W, hW, hWg⟩ := exists_alg (p := l) (AIP l).actT (eventually_actT_eq (AIP l))
    ((Units.coeHom _).comp f) (Units.continuous_val.comp hf)
    (fun g hg => congrArg Units.val (hfI g ((hI g).2 (norm_sub_lt_one_of_fix (AIP l) g hg))))
  refine ⟨(AIP l).ιA.mapMatrix W, (AIP l).ιA.mapMatrix W⁻¹, ?_, fun i j => (AIP l).ainf_image_mem_filtration_zero _ _,
    fun i j => (AIP l).ainf_image_mem_filtration_zero _ _, ?_, fun g hg => ?_⟩
  · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  · have h := hWg σ (frobenius _ l) fun m hm y hy => ((UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self y m hm hy).1 σ hσ).symm
    have h1 : W.map (WittVector.map (frobenius _ l)) = (zlW l (OCb l)).mapMatrix u * W := by
      conv_rhs => rw [← h, ← Matrix.mul_assoc]
      have e : (((Units.coeHom _).comp f) σ).map (zlW l (OCb l)) = (zlW l (OCb l)).mapMatrix (↑u⁻¹) := by
        rw [← hfσ]; rfl
      rw [e, ← map_mul, Units.mul_inv, map_one, Matrix.one_mul]
    have h2 := congrArg (AIP l).ιA.mapMatrix h1
    rw [map_mul] at h2
    convert h2 using 1
    · ext i j
      change (PP l).φB ((AIP l).ιA (W i j)) = (AIP l).ιA (WittVector.map (frobenius _ l) (W i j))
      rw [← (AIP l).ιA_φ, WittVector.frobenius_eq_map_frobenius]
    · congr 1
      ext i j
      exact (ιA_zlW (AIP l) Ti _).symm
  · have h := hWg 1 ((AIP l).actT g).toRingHom fun m hm y hy => by
      rw [map_one, RingAut.one_apply]
      exact (UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self y m hm hy).2 g hg
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul] at h
    ext i j
    change (PP l).actQ g ((AIP l).ιA (W i j)) = (AIP l).ιA (W i j)
    rw [← (AIP l).ιA_act]
    exact congrArg (AIP l).ιA (congrFun (congrFun h i) j)
end

section

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV IsLocalRing

def wtDer {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : X → Submodule O R) (x : R →ₐ[O] O)
    (E : Type) [Field E] [Algebra O E] (j : X) : Submodule E (R →ₗ[O] E) where
  carrier := {D | D ∈ PtDer ((Algebra.ofId O E).comp x) E ∧ HasWt 𝒜 j D}
  zero_mem' := ⟨zero_mem _, fun _ _ _ _ => rfl⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun i hi f hf => by
    rw [LinearMap.add_apply, ha.2 i hi f hf, hb.2 i hi f hf, add_zero]⟩
  smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun i hi f hf => by
    rw [LinearMap.smul_apply, ha.2 i hi f hf, smul_zero]⟩

def dimsL (w : ℤ × ℤ) : ℕ :=
  if w = wAl ∨ w = wBe ∨ w = wPs ∨ w = wTh ∨ w = 0 then 2 else if w ∈ wts then 1 else 0

def dimsP (w : ℤ × ℤ) : ℕ := if w = 0 then 2 else if w ∈ wts then 1 else 0

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {B : Type} [CommRing B] [Algebra c.O B]

def EqL (r : D.Gp l →* M4 B) : Prop :=
  (∀ g : D.Gp l, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧
    Ord ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O B (D.ps i g)) D.s0 r

def EqP (p : ℕ) (r : D.Gp p →* M4 B) : Prop :=
  (∀ g : D.Gp p, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧
    ∀ g : D.Gp p, (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker → r g = 1

structure IsContinuousLiftOfRZero [Algebra ℚ_[l] B] {E : Type} [CommRing E] [Algebra c.O E] (π : B →+* E) (v : ℕ)
    (r : D.Gp v →* M4 B) : Prop where
  red : mapRep π r = mapRep (algebraMap c.O E) (D.r0At v)
  cont : ∀ a b, QCont l fun g => r g a b

def IsFirstOrderDeformationOfRZero {E : Type} [CommRing E] [Algebra c.O E] (v : ℕ) (γ : D.Gp v → M4 E) (r' : D.Gp v →* M4 (DualNumber E)) :
    Prop :=
  ∀ g a b, r' g a b = ⟨algebraMap c.O E (D.r0At v g a b), (γ g * (D.r0At v g).map (algebraMap c.O E)) a b⟩

def FlagIn {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (h : (M4 K)ˣ) (κ : Fin 4 → H →* Kˣ) : Prop :=
  ∀ g, (∀ i j, j < i → ((h⁻¹ : (M4 K)ˣ) * r g * h : M4 K) i j = 0) ∧
    ∀ i, ((h⁻¹ : (M4 K)ˣ) * r g * h : M4 K) i i = (κ i g : K)

def PtOn {v : ℕ} (P : Cond c.O (D.rbarAt v)) {K : Type} [CommRing K] [Algebra c.O K] (r : D.Gp v →* M4 K) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O (D.rbarAt v) R) (y : R →ₐ[c.O] K),
    OnComp P (D.r0At v) ρ ∧ r = mapRep (y : R →+* K) ρ.hom

end UpperTheory.V.Loc
end
end
