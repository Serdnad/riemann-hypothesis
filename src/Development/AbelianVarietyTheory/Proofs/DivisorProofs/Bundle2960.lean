module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle545
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

open Matrix

theorem quad_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    (t • x) ⬝ᵥ M *ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ M *ᵥ x) := by
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem exists_nat_posDef {n : ℕ} (E A : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef) (hA : A.IsHermitian) :
    ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • E - A).PosDef := by
  have hq : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ E *ᵥ x := fun x hx => by
    simpa using hE.dotProduct_mulVec_pos hx
  have hc : ContinuousOn (fun x : Fin n → ℝ => (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun x hx => (hq x ?_).ne'
    rintro rfl
    simp at hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_bound_of_continuousOn hc
  refine ⟨⌈C⌉₊ + 1, fun κ hκ => PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_⟩
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hE.1.eq, hA.eq, star_trivial]
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']
    have hb := hC _ hy
    rw [quad_smul, quad_smul, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hx0.ne'))] at hb
    have hqx := hq x hx
    have h1 : (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x) ≤ C := le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at hb)
    have h2 : (x ⬝ᵥ A *ᵥ x) ≤ C * (x ⬝ᵥ E *ᵥ x) := (div_le_iff₀ hqx).1 h1
    have h3 : C < (κ : ℝ) := by
      have := Nat.le_ceil C
      have : ((⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ κ := by exact_mod_cast hκ
      push_cast at this
      linarith
    have h4 : C * (x ⬝ᵥ E *ᵥ x) < κ * (x ⬝ᵥ E *ᵥ x) := mul_lt_mul_of_pos_right h3 hqx
    have h5 : x ⬝ᵥ ((κ : ℝ) • E) *ᵥ x = κ * (x ⬝ᵥ E *ᵥ x) := by
      first
        | rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        | rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
        | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, h5]
    linarith

theorem exists_kappa (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ κ : ℕ, ∀ i : Fin 2,
      ((((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) +
        ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  have key : ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ →
      ((((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map
        (Int.cast : ℤ → ℝ)).PosDef := by
    intro m
    have hs : (m.transpose * (W + W.transpose) * m).transpose = m.transpose * (W + W.transpose) * m := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, add_comm,
        Matrix.mul_assoc]
    have hA : ((m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ)).IsHermitian := by
      refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [Matrix.map_apply, star_trivial]
      exact congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun hs i) j)
    obtain ⟨κ₀, h⟩ := exists_nat_posDef _ _ hW.1 hA
    refine ⟨κ₀, fun κ hκ => ?_⟩
    have e : (((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map
        (Int.cast : ℤ → ℝ) = (κ : ℝ) • (W + W.transpose).map (Int.cast : ℤ → ℝ) -
          (m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ) := by
      have e' : ((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose =
          (κ : ℤ) • (W + W.transpose) - m.transpose * (W + W.transpose) * m := by
        simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.mul_assoc]
        abel
      rw [e']
      ext a b
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact h κ hκ
  obtain ⟨κ₀, h₀⟩ := key (actMat W 0)
  obtain ⟨κ₁, h₁⟩ := key (actMat W 1)
  refine ⟨max κ₀ κ₁, fun i => ?_⟩
  fin_cases i
  · exact h₀ _ (le_max_left _ _)
  · exact h₁ _ (le_max_right _ _)

end GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

namespace GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

open GlobalTheory.SS GlobalTheory.CechPic


set_option maxRecDepth 20000 in
theorem exists_bound_relAmple : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ κ : ℕ, ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∀ i, Out.RelAmple P'.A (LB.LinComb P'.L (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]) := by
  intro W hW
  obtain ⟨κ, hκ⟩ := exists_kappa W hW
  refine ⟨κ, ?_⟩
  intro gQ K _ _ P' B _ _ M pr hPP hpr hE act _ hact i
  obtain ⟨hB, -, ⟨cub⟩, ha, -⟩ := hPP
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  let c := GlobalTheory.EighthPowerFactor.siegOne hG hB M.isLB gQ
  have hdiag : Out.RelAmple c.A c.diag :=
    GlobalTheory.EighthPowerFactor.relAmple_diag_lam hB M.isLB ⟨cub.t, cub.isGen⟩ ha
  have hamp := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG gQ 1 8 K _ (Sp K) (𝟙 _) c P'.A pr
    ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) hpr.1 hpr.2 hdiag (hκ i)
  have := P'.isAb.proper
  have hL := P'.isLB
  have hT := LB.isLB_linComb hL (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hT (LB.isLB_linComb c.isLB _ _) (N := 1) le_rfl ?_ hamp
  rw [one_smul]
  set f := act i with hf
  set m := actMat W i with hm
  have hflat := LB.isLB_linComb M.isLB (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))
  have hPL : cls P'.L hL = ∑ uv : Fin 8 × Fin 8,
      W uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
    rw [(cls_eq_iff hL hflat).2 hE, cls_linComb M.isLB, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have hlam : cls c.P c.isLB = lam (cls M.L M.isLB) (fst B B) (snd B B) := cls_cube_two M.isLB _ _ c.isLB
    erw [hlam]
    erw [pull_lam, lift_fst, lift_snd]
    rw [Fin.sum_univ_four]
    simp only [lam, lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, smul_sub, smul_add, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    module
  have hsub := (cls_eq_iff (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb c.isLB _ _)).2
    (GlobalTheory.BilinCalc.main (Sp K) c.A c.P c.isLB
      (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp K) c.A c.diag c.ab (pull_isLB c.isLB _) hdiag c.P c.isLB
        c.rig₁ c.rig₂)
      c.symm P'.A 8 8 pr W (m.transpose * W * m) m (by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc]))
  rw [cls_linComb c.isLB, cls_linComb c.isLB] at hsub
  have hpf : pull f.left (cls P'.L hL) = ∑ uv : Fin 8 × Fin 8,
      (m.transpose * W * m) uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by

    rw [hPL, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun uv _ => ?_) hsub.symm
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hact i uv.1, hact i uv.2]
    rfl
  rw [cls_linComb hL, cls_linComb c.isLB, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead]
  rw [pull_id, hpf, hPL]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_smul, mul_smul, Finset.sum_sub_distrib,
    Finset.smul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  first
    | exact neg_one_smul ℤ _
    | exact neg_one_zsmul _
    | simp

end GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericCube

theorem exists_iso_section {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X} (g : H ⟶ Y)
    (hg : g ≫ f = 𝟙 H) (w : LB.Iso (M.pull f) (L.pull ψ)) (hw : w.IsGen) :
    ∃ w' : LB.Iso M (L.pull (g ≫ ψ)), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) := by
  have mm : ∀ (y : H) (k : M.ι), y ∈ M.U k → g y ∈ (M.pull f).U (fun _ => k) := fun y k hy => mem_pull.2 (by
    have e : (g ≫ f) y = y := by rw [hg]; rfl
    exact (congrArg (· ∈ M.U k) e).mpr hy)
  have le : ∀ (j : L.ι) (k : M.ι), (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k ≤
      g ⁻¹ᵁ ((L.pull ψ).U (fun _ => j) ⊓ (M.pull f).U (fun _ => k)) := fun j k y hy =>
    ⟨mem_pull.2 (mem_pull₂.1 hy.1), mm y k hy.2⟩
  let w' : LB.Iso M (L.pull (g ≫ ψ)) :=
    ⟨fun p => res (le (p.1 PUnit.unit) p.2) (pullU g _ (w.s (fun _ => p.1 PUnit.unit, fun _ => p.2)))⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) :=
    fun Z r z j k hj hk => by
      have m : r z ∈ (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k := ⟨mem_pull₂.2 hj, hk⟩
      exact (gm_res r z (le j k) m _).trans (gm_pull r g z _ (le j k m) _)
  refine ⟨w', (isGen_iff w').2 fun Z r z j j' k k' hj hj' hk hk' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z (r ≫ g) z j j' (fun _ => k) (fun _ => k') hj hj' (mm _ k hk) (mm _ k' hk')
  rw [Geo.Tor.gm_pull_g M f (r ≫ g) z _ _ (mm _ k hk) (mm _ k' hk'), Category.assoc r g f, hg, Category.comp_id,
    Category.assoc] at e
  rw [hv Z r z j k hj hk, hv Z r z j' k' hj' hk']
  exact e

theorem cube_through_iso : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (∀ S, IntTerm.Ext U.toUnifPre (x S) (h S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1, 2}).left) (fun _ => JA (x {0, 1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}).left) (fun _ => JA (x {0}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}).left) (fun _ => JA (x {1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}).left) (fun _ => JA (x {2}).left)) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1}).left) (fun _ => JA (x {0, 1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 2}).left) (fun _ => JA (x {0, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1, 2}).left) (fun _ => JA (x {1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x ∅).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h ∅).left) (fun _ => JA (x ∅).left)) := by
  intro V _ _ _ _ D A G _ _ _ U w₀ hw₀ ρ hρ c x h x0 x01 x02 x12 x012 h0 h01 h02 h12 h012 hE z JA JG hJA hJG
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK V) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  obtain ⟨w, hw, hv⟩ := exists_iso_section U.gen.inv.left (congrArg (fun q => q.left) U.gen.inv_hom_id) w₀ hw₀
  have e := cub_w U.cubG c GlobalTheory.abelianSchemeLaws_all.1.globalFns A.isAb gp w hw
    (s' := jFK (R := V) (FractionRing V)) (s := jFK (R := V) (FractionRing V) ≫ jK V) (z := z) hJG hJA
    (x {0}) (x {1}) (x {2}) _ _ _ (hE {0}) (hE {1}) (hE {2})
  have k : ∀ S, Om w (s' := jFK (R := V) (FractionRing V)) z JG JA (x S) =
      Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
        (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h S).left) (fun _ => JA (x S).left) := fun S => by
    refine (hv _ (x S).left z _ _ (hJG ((x S).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V))) (hJA _)).trans ?_
    exact congrArg (fun q => Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
      (JG q) (fun _ => JA (x S).left)) (hE S)
  rw [← x012, ← x01, ← x02, ← x12, ← x0, k, k, k, k, k, k, k, k] at e
  refine Eq.trans ?_ (congrArg (· * _) e.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, id]
  abel

end GlobalTheory.GenericCube
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.IntTerm


open GlobalTheory.Poinc.ThetaOne in
theorem coef_eq_theta_value : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ₀ : FractionRing V, ∀ (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b), w.IsGen → ∀ (mu : D.X) (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z (coef s g' w mu) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z κ₀ * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ s
  obtain ⟨κ₀, hκ, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) s
  refine ⟨κ₀, fun g' w hw mu z J hJ => ?_⟩
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let ρ : TF (R := V) (FractionRing V) ⟶ DegPre.BF D (FractionRing V) := lift (𝟙 _) g'.b
  have hρ₁ : ρ ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have hρ₂ : ρ ≫ DegPre.prB D (FractionRing V) = g'.b := lift_snd _ _

  have s0 : ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ (DegPre.BF D (FractionRing V)).left),
      sval (s.s 0) r z J = GlobalTheory.FieldBaseChange.constVal (r ≫ GlobalTheory.FieldBaseChange.famBase D (FractionRing V)) z κ₀ *
        sval θ (r ≫ (DegPre.prB D (FractionRing V)).left) z J := by
    intro r
    have h1 : (GlobalTheory.FieldBaseChange.famProj D (FractionRing V) 1 0 s) = κ₀ • termF D (FractionRing V) 1 0 θ := hκ
    have h2 := congrArg (fun t : GlobalTheory.FieldBaseChange.FamTerm D (FractionRing V) 1 0 => sval (L := D.P.L) t r z J) h1
    refine h2.trans ?_
    rw [GlobalTheory.FieldBaseChange.sval_smul' hJ]
    congr 1
    exact GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ
  have key : ∀ x, x = 0 + 1 • mu →
      GlobalTheory.UT.cst (FractionRing V) z (coef s g' w x) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val =
      GlobalTheory.UT.cst (FractionRing V) z κ₀ *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val *
        sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s x) (𝟙 _) z J).val *
        (Geo.Tor.val w (𝟙 _) z J).val := by
    rintro x rfl
    have a := GlobalTheory.UT.CoefBasic.isCoef_coef g' hw (0 + 1 • mu) s z J hJ
    rw [pow_one] at a
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := FractionRing V) hG 1 mu 0
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe mu 0 u hu hc) _ ρ.left z J hJ
    have v := hv u hu hc _ ρ z J hJ
    rw [GlobalTheory.UU.uVal_one D (FractionRing V) _ _ _ hJ, _root_.one_mul, hρ₁] at v
    have m := GlobalTheory.UU.val_famMult_one D (FractionRing V) (𝟙 _) hJ mu 0
    rw [Over.id_left, Category.id_comp] at m
    have m' := congrArg Units.val m
    rw [Units.val_mul] at m'
    have ps : ∀ y, y = mu → (Geo.Tor.val (D.psi y) (jFK (R := V) (FractionRing V)) z J).val =
        (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J).val := by
      rintro _ rfl; rfl
    rw [ps _ (add_zero mu)] at m'
    have b₁ : ρ.left ≫ (DegPre.trF D (FractionRing V) mu).left ≫ GlobalTheory.FieldBaseChange.famBase D (FractionRing V) = 𝟙 _ := by
      rw [GlobalTheory.FieldBaseChange.trF_famBase]
      exact congrArg (fun q => q.left) hρ₁
    have b₂ : (ρ.left ≫ (DegPre.trF D (FractionRing V) mu).left) ≫ (DegPre.prB D (FractionRing V)).left =
        (padd D.P.A (DegPre.cT D _ mu) g'.b).left := by
      rw [← Over.comp_left, ← Over.comp_left, Category.assoc, DegPre.trF, lift_snd,
        GlobalTheory.IntFam.TermLift.comp_padd, hρ₂, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
      exact congrArg (fun q => Over.Hom.left q)
        (show padd D.P.A g'.b (DegPre.cT D _ mu) = padd D.P.A (DegPre.cT D _ mu) g'.b from mul_comm _ _)
    rw [s0, Category.assoc, b₁, b₂] at e
    rw [a, e, v]
    have c₀ : GlobalTheory.FieldBaseChange.constVal (𝟙 (TF (R := V) (FractionRing V)).left) z κ₀ = GlobalTheory.UT.cst (FractionRing V) z κ₀ := rfl
    rw [c₀]
    simp only [id]
    linear_combination (GlobalTheory.UT.cst (FractionRing V) z κ₀ * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J *
      (Geo.Tor.val (g'.s (0 + 1 • mu)) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val) * m'
  have := key mu (by rw [zero_add, one_smul])
  exact this

end GlobalTheory.Poinc.IntTerm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ g) z U a = (f.stalkMap z).hom (gs g (f z) U a) := by
  rw [← gs_pull f g z U h a, gs_eq f z _ h, gs_eq g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).symm

theorem formEq_famφB_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) {Y : Scheme.{0}} (h : Y ⟶ D.P.A.left) :
    FormEq (fun i => h ≫ D.famφB 0 i) (DegPre.famε 1) (fun _ : Fin 1 => h) (fun _ => (1 : ℤ)) := by
  intro U _ hh
  have e0 : D.famφB 0 0 = 𝟙 _ := rfl
  have e1 : D.famφB 0 1 = 𝟙 _ := by
    show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
    rw [ThetaOne.c_zero, MonObj.comp_one]
    show ((𝟙 D.P.A) * 1).left = _
    rw [_root_.mul_one]; rfl
  have e2 : D.famφB 0 2 = D.famφB 0 3 := by
    show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
    rw [ThetaOne.c_zero, MonObj.comp_one]
    rfl
  simp only [Fin.prod_univ_four, Fin.prod_univ_one, e0, e1, e2]
  simp [DegPre.famε]

theorem exists_unitAt_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ N : ℕ, 2 ≤ N → IsUnit (N : V) → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)), IntTerm.Exhausts D.P N b → ∀ a : 𝟙_ (Over (Sp V)) ⟶ D.P.A, ∃ c, IntTerm.UnitAt D θ (a * b c) := by
  intro V _ _ _ D θ hθ N hN hNV C b hb a
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  let k := AlgebraicClosure (ResidueField V)
  let f : V →+* k := (algebraMap (ResidueField V) k).comp (residue V)
  let r : Sp k ⟶ Sp V := Spec.map (CommRingCat.ofHom f)
  have hNk : (N : k) ≠ 0 := by
    have := (hNV.map f).ne_zero
    rwa [map_natCast] at this
  let θ' := ThetaOne.pullTo D f θ
  have hbasis := hθ k f θ' (ThetaOne.isPullSecLC_pullTo D f θ)
  obtain ⟨j₀, hj₀⟩ := ThetaOne.exists_ne_zero D f θ' hbasis
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB (formEq_famφB_zero D (snd (Over.mk r) D.P.A).left) θ'
  have hne : SecM.ofSec D.P.A (L := D.P.L) (a := 1) (T := Over.mk r) th ≠ 0 := by
    intro h0
    apply hj₀
    have hz : ∀ j, th.f j = 0 := fun j => congrFun (congrArg Subtype.val h0) j
    refine sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j₀
    rw [← hth _ (𝟙 _) y J hJ]
    show gs _ y _ (th.f _) = gs _ y _ 0
    erw [hz]
    have gz : ∀ {Y : Scheme.{0}} (y : Y) (U : Y.Opens), gs (𝟙 Y) y U 0 = 0 := fun y U => by
      unfold gs; split_ifs <;> simp only [map_zero]
    exact (gz _ _).trans (gz _ _).symm
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P r hN hNk th hne
    (toUnit (Over.mk r) ≫ a)
  obtain ⟨c, hc⟩ := hb k r y hy
  refine ⟨c, ?_⟩
  have hmul : (toUnit (Over.mk r) ≫ a) * y = toUnit (Over.mk r) ≫ (a * b c) := by rw [hc, MonObj.comp_mul]
  rw [hmul] at hu
  let g := a * b c
  let q : Sp k := closedPoint k
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h1 := hu q J hJ
  have hρ : (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left ≫ (snd (Over.mk r) D.P.A).left = r ≫ g.left := by
    rw [← Over.comp_left, ptSecT, lift_snd, Over.comp_left]
    congr 1
  have hθ'e : θ' = H1.SectionArithmetic.pullSec θ (snd (Over.mk r) D.P.A).left :=
    SecOps.sec_ext fun j => ThetaOne.isPullSecLC_pullTo D f θ j
  have h2 : IsUnit (sval θ (r ≫ g.left) q J) := by
    have e := hth _ (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left q J hJ
    rw [← hρ, ← H1.SectionArithmetic.sval_pullSec θ _ _ q hJ, ← hθ'e, ← e]
    exact h1
  have hrq : r q = closedPoint V := by
    show (Spec.map (CommRingCat.ofHom f)).base (closedPoint k) = _
    rw [Spec.map_base]
    exact IsLocalRing.comap_closedPoint f
  refine ⟨fun σ => J (r ≫ σ), fun σ => ?_, ?_⟩
  · have := hJ (r ≫ σ)
    rwa [Scheme.Hom.comp_apply, hrq] at this
  · rw [sval_of θ (r ≫ g.left) q J (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) (fun i => by rw [Category.assoc])] at h2
    have hm : g.left (r q) ∈ (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U
        (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) :=
      show g.left (r q) ∈ LB.wchart D.P.L (D.famφB 0) (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) from Set.mem_iInter.2 fun i => by
        have := hJ (r ≫ g.left ≫ D.famφB 0 i)
        simpa [Scheme.Hom.comp_apply] using this
    have h2' : IsUnit ((r.stalkMap q).hom (gs g.left (r q) _ (θ.f (fun i => J (r ≫ g.left ≫ D.famφB 0 i))))) := by
      rw [← gs_comp_stalkMap r g.left q _ hm]; exact h2
    have h3 := isUnit_of_map_unit (r.stalkMap q).hom _ h2'
    rw [hrq] at h3
    exact h3

end GlobalTheory.Poinc.IntTerm
end
end
