module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.PosModule

theorem main : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ {N : Type} [AddCommGroup N] [Module B N] [Module E N] [Module ℚ_[l] N] [IsScalarTower E B N] [IsScalarTower ℚ_[l] E N] [IsScalarTower ℚ_[l] B N] [FiniteDimensional ℚ_[l] N] [TopologicalSpace N] [IsModuleTopology ℚ_[l] N] [IsTopologicalAddGroup N] (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ContAction ρ ∧ Positive φ ρ := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχc w hw hχI N _ _ _ _ _ _ _ _ _ _ _ ρ hρ

  let bil : B →ₗ[ℚ_[l]] N →ₗ[ℚ_[l]] N := LinearMap.mk₂ ℚ_[l] (fun b x => b • x) (fun _ _ _ => add_smul _ _ _)
    (fun c b x => smul_assoc c b x) (fun _ _ _ => smul_add _ _ _)
    (fun c b x => by rw [← algebraMap_smul B c x, ← algebraMap_smul B c (b • x), smul_smul, smul_smul, mul_comm])
  have hbil : Continuous (fun p : B × N => p.1 • p.2) := IsModuleTopology.continuous_bilinear_of_finite_left bil
  have hcont : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ]
    exact hbil.comp ((hχc.comp continuous_fst).prodMk continuous_snd)
  refine ⟨hcont, ?_⟩
  have hcs : ContinuousConstSMul E N := ⟨fun c => by
    let f : N →ₗ[ℚ_[l]] N :=
      { toFun := fun x => c • x
        map_add' := smul_add c
        map_smul' := fun r x => by
          simp only [RingHom.id_apply]
          rw [← algebraMap_smul E r x, ← algebraMap_smul E r (c • x), smul_smul, smul_smul, mul_comm] }
    exact IsModuleTopology.continuous_of_linearMap f⟩
  have hIne : ∀ g, φ g ∈ Iq l → ∀ x, ρ g x = ((cycA l l E (φ g) ^ w : Eˣ) : E) • x := fun g hg x => by
    rw [hρ, hχI g hg, ← algebraMap_smul B (((cycA l l E (φ g) ^ w : Eˣ) : E)) x,
      ← algebraMap_cycA (E := E) (B := B), ← map_zpow]
    rfl
  have hcr : IsCr φ ρ := crUnr φ hφ ρ hcont w hIne
  have hdr : IsDr φ ρ := (isCrys_isDR_restrict_openSubgroup φ hφ ρ hcont).1 hcr
  refine ⟨hdr, ?_⟩

  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have : Module.Finite B N := Module.Finite.of_restrictScalars_finite ℚ_[l] B N
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := N)
  let ρB : Representation B G N :=
    { toFun := fun g => ((χ g : Bˣ) : B) • LinearMap.id
      map_one' := by ext; simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp only [map_mul, Units.val_mul, LinearMap.smul_apply, LinearMap.id_apply, Module.End.mul_apply, mul_smul] }
  let κ : G →* Eˣ := (Units.map (π : B →* E)).comp χ
  have hres : resCoef E ρB = ρ := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [hρ]
    rfl
  have hκ : κ ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
    refine ⟨w, hw, ⊤, by simp, fun g _ hg => ?_⟩
    apply Units.ext
    change π ((χ g : Bˣ) : B) = _
    rw [hχI g hg, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]
    exact π.commutes _
  rw [← hres]
  refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ ρB _ s (fun _ => κ) hs (fun _ => hκ) fun g j => ?_
  have hm : ((χ g : B) - algebraMap E B (π (χ g : B))) • s j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B N) :=
    Submodule.smul_mem_smul (by simp) trivial
  convert hm using 1
  rw [sub_smul, algebraMap_smul]
  rfl

end GlobalTheory.PosModule
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem push_mat_eq_mat_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : GQ l) : (push f r s).mat = (r s).mat.map f := by
  rfl
private theorem sh_push_eq_sh_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) (s : GQ l) : D.sh (push f r) a s = (D.sh r a s).map f := by
  ext i j
  simp only [Dat3.sh, Matrix.sub_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, push_mat_eq_mat_map, map_sub]
  split_ifs <;> simp
private theorem tr_push_algHom_eq_map_tr {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) : D.tr (push f r) a = f (D.tr r a) := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm

  simp only [Dat3.tr, sh_push_eq_sh_map, push_mat_eq_mat_map, h, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
private theorem map_dd_eq_dd_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) : f (D.dd r a) = D.dd (push f r) a := by
  simp only [Dat3.dd, tr_push_algHom_eq_map_tr, map_sub, map_mul, AlgHom.commutes]
private theorem map_coeff_charpoly_sub_prod_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : GQ l) (i : ℕ) : f (((r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) = (((push f r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) := by
  have h1 : (push f r s).mat.charpoly = (r s).mat.charpoly.map (f : C →+* C') := by
    rw [push_mat_eq_mat_map]
    exact Matrix.charpoly_map _ _
  have h2 : ∀ a : Fin 3, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))) = (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))).map (f : C →+* C') := by
    intro a
    simp
  rw [h1, Finset.prod_congr rfl (fun a _ => h2 a), ← Polynomial.map_prod, ← Polynomial.map_sub, Polynomial.coeff_map]
  rfl
private theorem map_sh_triple_prod_apply_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : Fin 3 → GQ l) (i j : Fin 3) : f ((D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2)) i j) = (D.sh (push f r) 0 (s 0) * D.sh (push f r) 1 (s 1) * D.sh (push f r) 2 (s 2)) i j := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  simp only [sh_push_eq_sh_map, h, Matrix.map_apply]


theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_map_algHom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)), (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) ∧ (∀ a, f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a) ∧ f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) := by
  intro l _ O _ _ _ D C C' _ _ _ _ f r
  refine ⟨?_, fun a => map_dd_eq_dd_push D f r a, ?_⟩
  · simp only [Dat3.ordIdeal]
    rw [Ideal.map_span, Set.image_union]
    congr 2
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, rfl⟩, rfl⟩
        exact ⟨s, hs, i, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
      · rintro ⟨s, hs, i, rfl⟩
        exact ⟨_, ⟨s, hs, i, rfl⟩, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, j, rfl⟩, rfl⟩
        exact ⟨s, hs, i, j, map_sh_triple_prod_apply_eq_push D f r s i j⟩
      · rintro ⟨s, hs, i, j, rfl⟩
        exact ⟨_, ⟨s, hs, i, j, rfl⟩, map_sh_triple_prod_apply_eq_push D f r s i j⟩
  · simp only [Dat3.del, map_mul, map_natCast, map_dd_eq_dd_push]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem sh_s0_eq_diagonal_psi_sub_psi {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (b : Fin 3) : D.sh r b D.s0 = Matrix.diagonal (fun c => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ c D.s0) - algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
  rw [Dat3.sh, h, Matrix.scalar_apply, Matrix.diagonal_sub]
private theorem tr_lemma_2 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (a : Fin 3) : D.tr r a = algebraMap O C (D.cc a) * (r D.fr).mat a a := by
  rw [Dat3.tr, sh_s0_eq_diagonal_psi_sub_psi D r h, sh_s0_eq_diagonal_psi_sub_psi D r h, Matrix.diagonal_mul_diagonal, Matrix.trace, Fin.sum_univ_three]
  simp only [Matrix.diag, Matrix.diagonal_mul, Dat3.cc, map_mul, map_sub]
  fin_cases a <;> simp <;> ring


theorem _root_.GlobalTheory.T.ordinary_derivative_entry_formula : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)), (r (GlobalTheory.OrdLoc.s0 D)).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D))) → ∀ a : Fin 3, GlobalTheory.OrdLoc.dd D r a = algebraMap O C (GlobalTheory.OrdLoc.cc D a * GlobalTheory.OrdLoc.cc D (a + 1)) * ((r (GlobalTheory.OrdLoc.fr D)).mat a a - algebraMap O C ((cycA l l O (GlobalTheory.OrdLoc.fr D) : Oˣ) : O) * (r (GlobalTheory.OrdLoc.fr D)).mat (a + 1) (a + 1)) := by
  intro l _ O _ _ _ D C _ _ r h a
  simp only [Dat3.dd, tr_lemma_2 D r h, map_mul]
  ring
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.saturatingElement_notMem_minimalPrimes_reducedOrdinaryIdeal : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)), ∀ P ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes, GlobalTheory.OrdLoc.del D U.r.hom ∉ P := by
  intro l _ O _ _ _ D U P hP hdel
  have hmem : ∀ a, a ∈ D.IY U ↔ ∃ n, D.del U.r.hom ^ n * a ∈ D.ordIdeal U.r.hom := by
    intro a
    rw [UpperTheory.V.Loc.Dat3.IY.eq_1]
    rfl
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hdel
  apply hy
  rw [UpperTheory.V.Loc.Dat3.Icr.eq_1] at hxy ⊢
  obtain ⟨k, hk⟩ := hxy
  obtain ⟨n, hn⟩ := (hmem _).1 hk
  refine ⟨k, (hmem _).2 ⟨n + k, ?_⟩⟩
  have e : D.del U.r.hom ^ (n + k) * y ^ k = D.del U.r.hom ^ n * (D.del U.r.hom * y) ^ k := by
    ring
  rw [e]
  exact hn
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.isLCrystalline_conjBy_invariant : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG (m := 3) (R := B)) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  first | exact @GlobalTheory.LCrConj.main | exact GlobalTheory.LCrConj.main | (intros; apply GlobalTheory.LCrConj.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]

theorem hl_normal' (D : Dat3 l O) : D.HL.Normal := by
  unfold Dat3.HL; infer_instance

theorem hl_isOpen' (D : Dat3 l O) : IsOpen (D.HL : Set (GQ l)) := by
  have e : (D.η.ker : Set (GQ l)) = (D.Kv.1.fixingSubgroup : Set (GQ l)) := by
    ext g; exact D.η_ker g
  have h1 : IsOpen (D.η.ker : Set (GQ l)) := by
    rw [e]; haveI := D.Kv.2; exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  exact h1.inter D.τ_open

theorem finiteIndex_of_open' (H : OpenSubgroup (GQ l)) : (H : Subgroup (GQ l)).FiniteIndex := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_isFr (D : Dat3 l O) : ∃ σ, IsFr D σ := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  haveI hHn : D.HL.Normal := hl_normal' D
  have hHo : IsOpen (D.HL : Set (GQ l)) := hl_isOpen' D
  obtain ⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩ := iqBasic l
  haveI : D.HL.FiniteIndex := finiteIndex_of_open' ⟨D.HL, hHo⟩
  set N : Subgroup (GQ l) := D.HL ⊔ Iq l with hN
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  haveI : N.Normal := Subgroup.sup_normal _ _
  set q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)
  set m := orderOf q with hm
  have hm1 : 1 ≤ m := orderOf_pos q
  have hmN : σ₀ ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one q
  obtain ⟨h, hh, i₀, hi₀, hhi⟩ := Subgroup.mem_sup_of_normal_right.1 hmN
  let φ := QuotientGroup.mk' (Iq l)
  have hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l := fun {x} => QuotientGroup.eq_one_iff x
  have hφm : φ σ₀ ^ m = φ h := by
    rw [← map_pow, ← hhi, map_mul, hφ.2 hi₀, mul_one]
  refine ⟨h, ⟨hh, ?_⟩, σ₀, m, hσ₀, hm1, ?_⟩
  ·
    rw [eq_top_iff]
    intro g _
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    rw [mem_closure_iff]
    intro U hU hgU
    have hdense := frobDense σ₀ hσ₀
    have hV : IsOpen (D.HL.subtype '' U) := (hHo.isOpenEmbedding_subtypeVal).isOpenMap U hU
    have hcl : (D.HL.subtype g) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [← Subgroup.topologicalClosure_coe, hdense]; trivial
    obtain ⟨x, ⟨u, huU, rfl⟩, hxT⟩ := mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩
    obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.1 hxT
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    change i * σ₀ ^ k = (u : GQ l) at hiz
    have hkN : σ₀ ^ k ∈ N := by
      have : σ₀ ^ k = i⁻¹ * (u : GQ l) := by rw [← hiz]; group
      rw [this]
      exact N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)
    have hdvd : (m : ℤ) ∣ k := by
      rw [hm, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]; exact hkN
    obtain ⟨j, rfl⟩ := hdvd
    have hφu : φ (u : GQ l) = φ h ^ j := by
      rw [← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]
    have hy : (u : GQ l) * h ^ (-j) ∈ Iq l := by
      rw [← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]
    refine ⟨u, huU, ?_⟩
    have e : u = (⟨(u : GQ l) * h ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hh _)⟩ : ↥D.HL) * (⟨h, hh⟩ : ↥D.HL) ^ j := by
      ext; simp
    rw [SetLike.mem_coe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  · rw [← hhi]; simpa using Subgroup.inv_mem _ hi₀

theorem fr_isFr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O),
    GlobalTheory.OrdLoc.IsFr D (GlobalTheory.OrdLoc.fr D) := by
  intro l _ O _ _ _ D
  exact Classical.epsilon_spec (exists_isFr D)

end GlobalTheory.OrdLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem hl_basic : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), D.HL.Normal ∧ IsOpen (D.HL : Set (GQ l)) ∧ IsOpenEmbedding D.HL.subtype ∧ (∀ s ∈ D.HL, s ∈ Iq l → D.Ψ s = cycA l l O s ^ D.e) ∧ GlobalTheory.OrdLoc.IsInertiaInfiniteCyclotomic D (GlobalTheory.OrdLoc.s0 D) := by
  intro l _ O _ _ _ D
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    haveI := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have ho : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  have hex : ∃ s, IsInertiaInfiniteCyclotomic D s := by
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := ((cycInertia l).2 D.HL ho).2
    exact ⟨s, hs1, hs2, hs⟩
  refine ⟨inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal, ho, ho.isOpenEmbedding_subtypeVal, fun s hs hi => ?_,
    Classical.epsilon_spec hex⟩
  have ht : D.τ s = 1 := hs.2
  rw [D.Ψ_I s hi, ht, mul_one]

end GlobalTheory.OrdLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.FibreGlue

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (πC : C →ₐ[E] E) (hπC : ∀ a, πC a = 0 → IsNilpotent a) (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T] [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T] [IsScalarTower ℚ_[l] E T] (πT : T →ₐ[E] E) (hπT : ∀ a, πT a = 0 → IsNilpotent a) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C), π.comp p₁ = πT → πC.comp p₂ = πT → (∀ b c, π b = πC c → ∃! t, p₁ t = b ∧ p₂ t = c) → ∀ (r₁ : GQ l →* GG (m := 3) (R := B)) (r₂ : GQ l →* GG (m := 3) (R := C)), D.InDcr (π : B →+* E) r₁ → D.InDcr (πC : C →+* E) r₂ → ∃ r : GQ l →* GG (m := 3) (R := T), D.InDcr (πT : T →+* E) r ∧ (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ C _ _ _ _ _ _ _ _ _ _ πC hπC T _ _ _ _ _ _ _ _ _ _ πT hπT p₁ p₂ h1 h2 huniq r₁ r₂ hr₁ hr₂
  have hpt : ∀ x, π (p₁ x) = πC (p₂ x) := fun x => by
    rw [← AlgHom.comp_apply, h1, ← AlgHom.comp_apply, h2]
  have hf : ∀ x y, (p₁ : T →+* B) x = (p₁ : T →+* B) y → (p₂ : T →+* C) x = (p₂ : T →+* C) y → x = y := by
    intro x y e1 e2
    obtain ⟨t, -, ht⟩ := huniq (p₁ x) (p₂ x) (hpt x)
    exact (ht x ⟨rfl, rfl⟩).trans (ht y ⟨e1.symm, e2.symm⟩).symm
  have hq : ∀ b c, (π : B →+* E) b = (πC : C →+* E) c → ∃ x, (p₁ : T →+* B) x = b ∧ (p₂ : T →+* C) x = c :=
    fun b c e => (huniq b c e).exists
  have hred : (GG.map (π : B →+* E)).comp r₁ = (GG.map (πC : C →+* E)).comp r₂ := hr₁.red.trans hr₂.red.symm
  have hglue : ∃ r : GQ l →* GG (m := 3) (R := T),
      (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
    have hg : ∀ g, GG.map (π : B →+* E) (r₁ g) = GG.map (πC : C →+* E) (r₂ g) :=
      fun g => DFunLike.congr_fun hred g
    choose n hn₁ hn₂ using fun g =>
      OrdinaryDeformation.glue_GL (p₁ : T →+* B) (p₂ : T →+* C) (π : B →+* E)
        (πC : C →+* E) hf hq (r₁ g).left (r₂ g).left (congrArg SemidirectProduct.left (hg g))
    let x : GQ l → GG (m := 3) (R := T) := fun g => ⟨n g, (r₁ g).right⟩
    have hx₁ (g : GQ l) : GG.map (p₁ : T →+* B) (x g) = r₁ g :=
      SemidirectProduct.ext (hn₁ g) rfl
    have hx₂ (g : GQ l) : GG.map (p₂ : T →+* C) (x g) = r₂ g := by
      refine SemidirectProduct.ext (hn₂ g) ?_
      simpa only [GG.map_right] using congrArg SemidirectProduct.right (hg g)
    have hsep {a b : GG (m := 3) (R := T)}
        (ha : GG.map (p₁ : T →+* B) a = GG.map (p₁ : T →+* B) b)
        (hb : GG.map (p₂ : T →+* C) a = GG.map (p₂ : T →+* C) b) : a = b := by
      refine SemidirectProduct.ext (Units.ext (Matrix.ext fun i j => hf _ _ ?_ ?_)) ?_
      · exact congrArg (fun u => u.mat i j) ha
      · exact congrArg (fun u => u.mat i j) hb
      · simpa only [GG.map_right] using congrArg SemidirectProduct.right ha
    refine ⟨MonoidHom.mk' x (fun g g' => hsep ?_ ?_), MonoidHom.ext hx₁, MonoidHom.ext hx₂⟩
    · rw [map_mul, hx₁, hx₁, hx₁, map_mul]
    · rw [map_mul, hx₂, hx₂, hx₂, map_mul]
  obtain ⟨r, e1, e2⟩ := hglue
  refine ⟨r, ?_, e1, e2⟩
  let f₁ := (p₁.restrictScalars ℚ_[l]).toLinearMap
  let f₂ := (p₂.restrictScalars ℚ_[l]).toLinearMap
  rw [← e1] at hr₁
  rw [← e2] at hr₂
  have hc : ∀ a b, QCont l fun g => (r g).mat a b := fun a b =>
    OrdinaryDeformation.qcont_pair f₁ f₂ hf (hr₁.cont a b) (hr₂.cont a b)
  have hm : HasMult D.η r := hr₁.mult
  have hπcomp : (π : B →+* E).comp (p₁ : T →+* B) = (πT : T →+* E) :=
    RingHom.ext fun x => by
      change π (p₁ x) = πT x
      rw [← AlgHom.comp_apply, h1]
  refine ⟨hm, ?_, hc, ?_⟩
  · rw [← hπcomp]
    exact hr₁.red
  obtain ⟨ρ₁, hρ₁, hcr₁⟩ := hr₁.cr
  obtain ⟨ρ₂, hρ₂, hcr₂⟩ := hr₂.cr
  let _ : TopologicalSpace B := moduleTopology ℚ_[l] B
  have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  let _ : TopologicalSpace C := moduleTopology ℚ_[l] C
  have : IsModuleTopology ℚ_[l] C := ⟨rfl⟩
  have : IsTopologicalRing C := IsModuleTopology.isTopologicalRing ℚ_[l] C
  let _ : TopologicalSpace T := moduleTopology ℚ_[l] T
  have : IsModuleTopology ℚ_[l] T := ⟨rfl⟩
  have : IsTopologicalRing T := IsModuleTopology.isTopologicalRing ℚ_[l] T
  have c₁ : ContAction (resCoef ℚ_[l] (colRep ρ₁)) := OrdinaryDeformation.cont_col ρ₁ fun a b => by
    simp only [hρ₁]
    exact (hr₁.cont a b).comp (continuous_subtype_val (p := fun g => g ∈ D.HL))
  have c₂ : ContAction (resCoef ℚ_[l] (colRep ρ₂)) := OrdinaryDeformation.cont_col ρ₂ fun a b => by
    simp only [hρ₂]
    exact (hr₂.cont a b).comp (continuous_subtype_val (p := fun g => g ∈ D.HL))
  have cprod : ContAction ((resCoef ℚ_[l] (colRep ρ₁)).prod (resCoef ℚ_[l] (colRep ρ₂))) :=
    (c₁.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (c₂.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hHL := OrdinaryDeformation.HL_emb D
  have hprod := (isCrys_isDR_prod _ hHL _ _ c₁ c₂).1 hcr₁ hcr₂
  refine ⟨(glPart D.η r hm).comp (Subgroup.inclusion inf_le_left), fun g => rfl, ?_⟩
  refine ((isCrys_isDR_sub_quot _ hHL _ _ (OrdinaryDeformation.cont_col _ fun a b => ?_) cprod
    ((f₁.compLeft (Fin 3)).prod (f₂.compLeft (Fin 3))) fun g x => ?_).1
    (fun x y h => ?_)).1 hprod
  · exact (hc a b).comp continuous_subtype_val
  · refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · change _ = Matrix.mulVec (ρ₁ g : Matrix (Fin 3) (Fin 3) B) _ a
      rw [hρ₁]
      exact RingHom.map_mulVec (p₁ : T →+* B) _ x a
    · change _ = Matrix.mulVec (ρ₂ g : Matrix (Fin 3) (Fin 3) C) _ a
      rw [hρ₂]
      exact RingHom.map_mulVec (p₂ : T →+* C) _ x a
  · exact funext fun a => hf _ _ (congrFun (congrArg Prod.fst h) a) (congrFun (congrArg Prod.snd h) a)

end GlobalTheory.FibreGlue
end
