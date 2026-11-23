module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle196
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Algebra.WithConv
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.IndefR Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.AdFormsModel

section

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ι : Γ →* G} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {I : Type} {y : I → G}

theorem eq_zero_of_reps (hy : Bridge.IsReps ι J y) {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ)
    (h0 : ∀ i, F (y i) = 0) : F = 0 := by
  funext h
  obtain ⟨i, ⟨γ, k, rfl⟩, -⟩ := hy h
  have := hF γ (y i) k
  rw [this, h0 i]
  simp

theorem finiteDimensional_adForms [FiniteDimensional ℂ W] [Finite I] (hy : Bridge.IsReps ι J y) :
    FiniteDimensional ℂ (Bridge.AdForms ι ρ J χ) := by
  let ev : Bridge.AdForms ι ρ J χ →ₗ[ℂ] (I → W) :=
    (LinearMap.funLeft ℂ W y).comp (Bridge.AdForms ι ρ J χ).subtype
  refine FiniteDimensional.of_injective ev ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro F hF
  exact Subtype.ext (eq_zero_of_reps hy F.2 fun i => congrFun hF i)

theorem adInner_self_pos [Fintype I] (hy : Bridge.IsReps ι J y) (hs : ∀ i, Finite (Bridge.stab ι J (y i)))
    {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ) (hne : F ≠ 0) : 0 < (Bridge.adInner ι J y F F).re := by
  have hre : (Bridge.adInner ι J y F F).re =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℝ))⁻¹ * ‖F (y i)‖ ^ 2 := by
    unfold Bridge.adInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    have : ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ((‖F (y i)‖ : ℝ) : ℂ) ^ 2 =
        ((((Nat.card (Bridge.stab ι J (y i)) : ℝ))⁻¹ * ‖F (y i)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    exact (congrArg Complex.re this).trans (Complex.ofReal_re _)
  rw [hre]
  obtain ⟨i, hi⟩ : ∃ i, F (y i) ≠ 0 := by
    by_contra hcon
    exact hne (eq_zero_of_reps hy hF fun i => by
      by_contra h
      exact hcon ⟨i, h⟩)
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩
  haveI := hs i
  have h1 : (0 : ℝ) < (Nat.card (Bridge.stab ι J (y i)) : ℝ) := by exact_mod_cast Nat.card_pos
  have h2 : 0 < ‖F (y i)‖ := norm_pos_iff.2 hi
  positivity

end

theorem exists_hmod_adForms : ∀ (G Γ W : Type) [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (I : Type)
    [Fintype I] (y : I → G), Bridge.IsReps ι J y → (∀ i, Finite (Bridge.stab ι J (y i))) →
    ∃ M : HMod (G → W), M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y) := by
  intro G Γ W _ _ _ _ _ ι ρ J χ I _ y hy hs
  refine GlobalTheory.HilbertModel.exists_hmod (G → W) _ _ (finiteDimensional_adForms hy) ?_
    (fun F hF hne => adInner_self_pos hy hs hF hne)
  intro a _ b _ d _ c
  constructor
  · simp only [Bridge.adInner, Pi.add_apply, Pi.smul_apply, inner_add_right, inner_smul_right, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp only [Bridge.adInner, star_sum, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_conj_symm (b (y i)) (a (y i))]
    rfl

end GlobalTheory.AdFormsModel
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatLevel

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_nsmul_smul_mem {m n : ℕ} (U : AddSubgroup (Mx D m n)) (hU : IsOpen (U : Set (Mx D m n)))
    (y : Mx D m n) : ∃ N : ℕ, 0 < N ∧ ∀ α ∈ intAf D.host.F,
      N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) ∈ U := by
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F → Mx D m n := fun α => Matrix.of fun i j => pairA D.host.F 0 α • y i j
  have hp : Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 α :=
    continuous_const.prodMk continuous_id
  have hφ : Continuous φ := continuous_pi fun i => continuous_pi fun j => hp.smul continuous_const
  have h0 : φ 0 = 0 := Matrix.ext fun i j => zero_smul (AF D.host.F) (y i j)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele D.host.F (φ ⁻¹' U)
    (hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (h0 ▸ U.zero_mem)))
  refine ⟨N, hN, fun α hα => ?_⟩
  have h1 : φ (N • α) ∈ U := h α hα
  have h2 : φ (N • α) = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) := by
    refine Matrix.ext fun i j => ?_
    have e1 : pairA D.host.F 0 (N • α) = N • pairA D.host.F 0 α :=
      Prod.ext (show (0 : Ainf D.host.F) = N • 0 by rw [smul_zero]) rfl
    show pairA D.host.F 0 (N • α) • y i j = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * y i j)
    rw [e1, smul_assoc, Algebra.smul_def (pairA D.host.F 0 α)]
  rwa [h2] at h1

def actHom (S T : HSp D) (g : GA D S) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T g h) fun x y => by
    unfold actO
    rw [Matrix.mul_add, Matrix.add_mul]

theorem continuous_actO (S T : HSp D) (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [actO, Matrix.mul_apply]
  refine continuous_finsetSum _ fun k _ => Continuous.mul (continuous_finsetSum _ fun l _ =>
    continuous_const.mul ?_) continuous_const
  exact (continuous_apply k).comp (continuous_apply l)

theorem actO_map_inf (S T : HSp D) (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

def finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) : AddSubgroup (Mx D m n) :=
  (L.map (finPart D).toAddMonoidHom.mapMatrix).comap (finPart D).toAddMonoidHom.mapMatrix

theorem mem_finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) (x : Mx D m n) :
    x ∈ finSat L ↔ ∃ l ∈ L, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 := by
  have key : ∀ l : Mx D m n, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 ↔
      (finPart D).toAddMonoidHom.mapMatrix l = (finPart D).toAddMonoidHom.mapMatrix x := by
    intro l
    rw [one_smul, eq_comm (b := (finPart D).toAddMonoidHom.mapMatrix x), ← sub_eq_zero (a := (finPart D).toAddMonoidHom.mapMatrix x), ← map_sub]
    rfl
  simp only [key]
  rfl

theorem level_of_generators : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • u ∈ U) ∧ ∀ (g : GA D S) (h : GA D T), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D S T ΛS ΛT hS hT ⟨G, hG, _, hgen⟩
  have h1 : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        N • u ∈ U := by
    intro U hU
    choose M hM hMU using fun y : WO S T => exists_nsmul_smul_mem U hU y
    refine ⟨∏ y ∈ hG.toFinset, M y, Finset.prod_pos fun y _ => hM y, ?_⟩
    refine hgen (U.comap (nsmulAddMonoidHom (∏ y ∈ hG.toFinset, M y))) fun α hα u hu => ?_
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem M (hG.mem_toFinset.2 hu)
    show (∏ y ∈ hG.toFinset, M y) • _ ∈ U
    rw [hc, mul_comm, mul_smul]
    exact U.nsmul_mem (hMU u α hα) c
  refine ⟨h1, fun g h => ?_⟩
  have hop : IsOpen (finSat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) : Set (WO S T)) := by
    convert GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 1 one_pos using 1
    exact Set.ext fun x => mem_finSat _ x
  obtain ⟨N, hN, hNU⟩ := h1 ((finSat _).comap (actHom S T g h)) (hop.preimage (continuous_actO S T g h))
  refine ⟨N, hN, fun u hu => ?_⟩
  have h2 : actHom S T g h (N • u) ∈ finSat _ := hNU u hu
  obtain ⟨l, hl, hl0⟩ := (mem_finSat _ _).1 h2
  have h3 : (actHom S T g h (N • u)).map (infPart D) = 0 :=
    actO_map_inf S T g h (latO_fin (AddSubgroup.nsmul_mem _ hu N))
  have h4 := latO_fin hl
  have h5 : actHom S T g h (N • u) = l := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · exact (congrFun (congrFun h3 i) j).trans (congrFun (congrFun h4 i) j).symm
    · have h6 : finPart D (actHom S T g h (N • u) i j - (1 : ℕ) • l i j) = 0 := congrFun (congrFun hl0 i) j
      rwa [one_smul, RingHom.map_sub, sub_eq_zero] at h6
  rw [map_nsmul] at h5
  exact h5 ▸ hl

end GlobalTheory.LatLevel

end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothCyclic

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GardingVec GlobalTheory.LowTypeRestriction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Conj
variable {n : ℕ}

theorem conj_lie {J G A B X : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (h : Bᴴ * J * B = G)
    (hX : Xᴴ * J + J * X = 0) : (A * X * B)ᴴ * G + G * (A * X * B) = 0 := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hBA' : Aᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  calc (A * X * B)ᴴ * G + G * (A * X * B)
      = Bᴴ * (Xᴴ * (Aᴴ * Bᴴ) * J + J * (B * A) * X) * B := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_of_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (A * X * B)) = A * NormedSpace.exp (t • X) * B := by
  have hB : B = A⁻¹ := (Matrix.inv_eq_right_inv hAB).symm
  rw [hB, ← Matrix.exp_conj _ _ (IsUnit.of_mul_eq_one _ hAB)]
  simp

theorem list_prod_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun a => A * a * B).prod = A * l.prod * B := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  induction l with
  | nil => simp [hAB]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc A * a * B * (A * l.prod * B) = A * a * (B * A) * l.prod * B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem expProd_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) {k : ℕ}
    (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * B))).prod
      = A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * B := by
  rw [← list_prod_conj hAB, List.map_ofFn]
  simp only [exp_conj_of_mul hAB, Function.comp_def]

end Conj

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def lieJ (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem exp_memJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε :=
  exp_mem (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hX t

theorem expProd_memJ {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieJ ε) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ UJset ε :=
  list_prod_mem (G := Formalism.REAL.Jm ε) _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_memJ (hX i) _

theorem rep_mul (hσ : IsURepOn (UJset ε) σ) {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε)
    (v : H) : σ a (σ b v) = σ (a * b) v := by
  rw [hσ.1.2 _ ha _ hb]; rfl

def smSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | SmoothVec (lieJ ε : Set _) σ w}
  add_mem' := fun ha hb k Xs hX => by simpa only [map_add (f := _)] using (ha k Xs hX).add (hb k Xs hX)
  zero_mem' := fun k Xs _ => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c w hw k Xs hX => by simpa only [map_smul] using (hw k Xs hX).const_smul c

theorem hasDerivAt_dRep {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (dRep σ X w) 0 := by
  have h := (hw 1 (fun _ => X) fun _ => hX).comp (contDiff_pi.2 fun _ : Fin 1 => (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)))
  have h2 : ContDiff ℝ ∞ fun t : ℝ => σ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h
  exact (h2.differentiable (by simp) 0).hasDerivAt

theorem dRep_mem (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieJ ε) : dRep σ X w ∈ smSub ε σ := by
  intro k Xs hXs
  have h := hw (k + 1) (Fin.snoc Xs X) (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  have hs : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ => (Fin.snoc z.1 z.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simpa [Function.comp_def] using (contDiff_apply ℝ (fun _ => ℝ) j).comp (contDiff_fst (F := ℝ))
  have h2 : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ =>
      σ ((List.ofFn fun i => NormedSpace.exp (z.1 i • Xs i)).prod) (σ (NormedSpace.exp (z.2 • X)) w) := by
    convert h.comp hs using 2 with z
    rw [rep_mul hσ (expProd_memJ hXs _) (exp_memJ hX _)]
    simp only [Function.comp_def, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last, List.prod_append,
      List.prod_singleton]
  have h3 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (f := fun (t : Fin k → ℝ) (s : ℝ) =>
      σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (σ (NormedSpace.exp (s • X)) w))
      (g := fun _ => 0) h2 contDiff_const (by simp)
  convert h3.clm_apply (contDiff_const (c := (1 : ℝ))) using 2 with t
  exact (((σ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_dRep hw hX)).deriv.symm

variable {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}

section Transport
variable {P G : Matrix (Fin n) (Fin n) ℂ}

theorem smoothVec_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (w : H) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w ↔ w ∈ smSub ε σ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  constructor
  · intro hw k Xs hX
    have := hw k (fun i => P⁻¹ * Xs i * P) fun i => conj_lie h2 h (hX i)
    convert this using 2 with t
    rw [expProd_conj h2]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro hw k Xs hX
    simpa only [expProd_conj h1] using hw k (fun i => P * Xs i * P⁻¹) fun i => conj_lie h1 h' (hX i)

theorem sobCont_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) ℓ) : Sobolev₂ (lieJ ε : Set _) σ ℓ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  obtain ⟨S, C, hS, hb⟩ := hℓ
  have e : dRep (fun g => σ (P * g * P⁻¹)) = fun X w => dRep σ (P * X * P⁻¹) w := by
    funext X w
    simp only [dRep, exp_conj_of_mul h1]
  refine ⟨S.map fun l => l.map fun X => P * X * P⁻¹, C, fun l hl X hX => ?_, fun w hw => ?_⟩
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_lie h1 h' (hS l' hl' Y hY)
  · simpa only [e, List.map_map, Function.comp_def, List.foldr_map] using
      hb w ((smoothVec_transport hP h w).2 hw)

end Transport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sm_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ = smSub (M.ε τ) (M.σ τ) := by
  rw [← Submodule.span_eq (smSub (M.ε τ) (M.σ τ))]
  exact congrArg (Submodule.span ℂ) (Set.ext fun w => smoothVec_transport (M.fr_unit τ) (M.fr_gram τ) w)

end GlobalTheory.SmoothCyclic
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.RationalPoints

theorem Hf_nsmul (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (m n : ℕ) (y y' : TaylorLogMetric.VC D a b) :
    TaylorLogMetric.Hf D T (m • y) (n • y') = ((m * n : ℝ) : ℂ) * TaylorLogMetric.Hf D T y y' := by
  rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.Hf_eq, ← Nat.cast_smul_eq_nsmul ℂ m,
    ← Nat.cast_smul_eq_nsmul ℂ n, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.sq_smul_right]
  simp only [map_natCast]
  push_cast
  ring

theorem rational_points : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ), StandardLatticesGL3.Crv D cc dl → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → (∀ x : Matrix (Fin b) (Fin a) D.host.E, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' (dl • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc dl) x)) ∧ ∀ y y', StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y' → (∃ q : ℚ, (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc dl) y y').im = q) ∧ ∃ q : ℚ, (Real.sqrt D.host.d / 2 : ℝ) * TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc dl) y y = ((q : ℝ) : ℂ) := by
  intro D cc dl hc a b L L' hL hL'
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hK : StandardLatticesGL3.KLat D (TaylorLogMetric.tor0 D cc dl) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L L') :=
    Or.inr ⟨_, _, hL, hL', rfl⟩
  obtain ⟨-, -, h1, -, -, -, h5⟩ := GlobalTheory.ThetaLine.theta_line D hG cc dl hc a b _ hK
  refine ⟨fun x => GlobalTheory.ThetaInter.klat_mul_mem hG.1 hc.1.1 hK x, ?_⟩
  rintro y y' ⟨m, hm, hy⟩ ⟨n, hn, hy'⟩
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  constructor
  · obtain ⟨k, hk⟩ := h1 _ hy _ hy'
    rw [Hf_nsmul, Complex.im_ofReal_mul] at hk
    refine ⟨k / (m * n), ?_⟩
    push_cast
    rw [← hk]
    field_simp
  · obtain ⟨k, hk⟩ := h5 _ hy
    rw [TaylorLogMetric.qH, Hf_nsmul, Complex.re_ofReal_mul] at hk
    refine ⟨k / (m * m), Complex.ext ?_ ?_⟩
    · rw [Complex.re_ofReal_mul, Complex.ofReal_re]
      push_cast
      rw [← hk]
      field_simp
    · rw [Complex.im_ofReal_mul, Complex.ofReal_im, GlobalTheory.ThetaLine.im_Hf, GlobalTheory.ThetaLine.sq_self_im]
      simp

end GlobalTheory.RationalPoints
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetric_two_cocycle_sum_pow_mul : ∀ (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D), (∀ x y, c x y = c y x) → (∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) → ∀ (n : ℕ) (x y : Γ), ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y = ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y + c (x ^ n) (y ^ n) - c 1 1 := by
  first | exact @GlobalTheory.TwoCocycle.sum_pow_mul | exact GlobalTheory.TwoCocycle.sum_pow_mul | (intros; apply GlobalTheory.TwoCocycle.sum_pow_mul <;> assumption)
end
