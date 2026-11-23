module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_finset_isIntB_one_tmul (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type)
    (b : Module.Basis κ ℚ M) (x : M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  have hfin : (⋃ i ∈ ((b.repr x).support : Set κ), HeightOneSpectrum.Support ℤ (b.repr x i)).Finite :=
    (b.repr x).support.finite_toSet.biUnion fun i _ => HeightOneSpectrum.Support.finite ℤ (b.repr x i)
  refine ⟨hfin.toFinset, fun v hv i => ?_⟩
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  by_cases hi : b.repr x i = 0
  · rw [hi, map_zero]; exact zero_mem _
  · have h1 : v ∉ HeightOneSpectrum.Support ℤ (b.repr x i) := fun h =>
      hv (hfin.mem_toFinset.2 (Set.mem_biUnion (Finsupp.mem_support_iff.2 hi) h))
    have h2 : v.valuation ℚ (b.repr x i) ≤ 1 := not_lt.1 h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b.repr x i)
    rw [← h3] at h2
    convert h2 using 2
    rfl

end GlobalTheory.AdicSpan
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem _root_.GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (T : CDVR) (iK : K →+* T.Fr), letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x), m1'.φ = n'.φ ≫ m1.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → ∀ (i : Fin (Dw.mult ρ)) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) → u'' ≫ m1'.φ = y'.u ρ i → ∃ w'' : epsR T.Fr ⟶ t'.G, w''.left = u'' ∧ IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) v' w'' := by
  first | exact @GlobalTheory.PtDeg.frame_genFib_coords | exact GlobalTheory.PtDeg.frame_genFib_coords | (intros; apply GlobalTheory.PtDeg.frame_genFib_coords <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PtExt.CanMap

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def ext (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hs : IsSymCoc d.g) : G.RigExt :=
  G.rigMk (⟨d.coc, fun n ↦ ⟨GlobalTheory.T.rigidifiedPresentation_cocycle_mem_bialgebraSymmetricCocycles R A p G t c d hs n, GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq R A p G t c d n⟩⟩,
    ⟨d.om, fun n ↦ GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification R A p G t c d n⟩)

theorem ext_isCan (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hs : IsSymCoc d.g) :
    IsCan t c (ext t c d hs) :=
  ⟨d, _, _, fun _ ↦ rfl, fun _ ↦ rfl, rfl⟩

theorem exists_isCan (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) : ∃ x, IsCan t c x := by
  obtain ⟨d⟩ := GlobalTheory.T.nonempty_primitiveDeRhamTorsionTowerPresentation R A p G t c
  exact ⟨_, ext_isCan t c d (GlobalTheory.T.isSymmetricTwoCocycle_of_additiveStructure_torsor R A hA (fv d.f) d.g d.add)⟩

def canFun (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) : G.RigExt :=
  (exists_isCan t hA c).choose

theorem canFun_isCan (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) :
    IsCan t c (canFun t hA c) :=
  (exists_isCan t hA c).choose_spec

theorem isCan_iff (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) (x : G.RigExt) :
    IsCan t c x ↔ canFun t hA c = x :=
  ⟨fun h ↦ GlobalTheory.T.canonicalRigidifiedExtensionOfDeRhamClass_unique R A p G t c hA _ _ (canFun_isCan t hA c) h, fun h ↦ h ▸ canFun_isCan t hA c⟩

def canMap (t : G.TorsionTower A) (hA : IsAbelianScheme A) : primDR A →ₗ[R] G.RigExt where
  toFun := canFun t hA
  map_add' c c' := (isCan_iff t hA _ _).1
    ((GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul R A p G t).1 c c' _ _ (canFun_isCan t hA c) (canFun_isCan t hA c'))
  map_smul' r c := (isCan_iff t hA _ _).1
    ((GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul R A p G t).2 r c _ (canFun_isCan t hA c))

end GlobalTheory.PtExt.CanMap

theorem GlobalTheory.PtExt.exists_canMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A), IsAbelianScheme A →
      ∃ L : primDR A →ₗ[R] G.RigExt, ∀ c x, IsCan t c x ↔ L c = x :=
  fun _ _ _ _ _ _ t hA ↦ ⟨GlobalTheory.PtExt.CanMap.canMap t hA, GlobalTheory.PtExt.CanMap.isCan_iff t hA⟩
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

section Diag

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

theorem diag_inv_of_diag (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∀ i j, i ≠ j → (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro i j hij
  have h := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 i j
  rw [Subgroup.coe_inv, h, ht _ _ (fun e => hij (Fin.rev_injective e).symm), map_zero]

theorem diag_mul_mul_diag_apply (s u t : GU σ n)
    (hs : ∀ i j, i ≠ j → ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i j : Fin n) :
    (((s * u * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
        ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
    Finset.sum_eq_single j (fun b _ hb => by rw [ht b j hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single i (fun b _ hb => by rw [hs i b (Ne.symm hb), zero_mul]) (by simp)]

theorem diag_inv_mul_diag (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i : Fin n) :
    (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
  have h := diag_mul_mul_diag_apply t⁻¹ 1 t (diag_inv_of_diag t ht) ht i i
  rw [mul_one, inv_mul_cancel] at h
  simpa using h.symm

end Diag

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_cornerU_conj {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (k : Fin (n / 2))
    (t : GU σ n) (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (u : GU σ n) :
    Valued.v (cornerU k (t⁻¹ * u * t)) =
      WithZero.exp (2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) *
        Valued.v (cornerU k u) := by
  unfold cornerU
  rw [diag_mul_mul_diag_apply _ _ _ (diag_inv_of_diag t ht) ht]
  have h1 := diag_inv_mul_diag t ht (lo k)
  have h2 := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 (lo k) (lo k)
  rw [← Subgroup.coe_inv] at h2
  have h0 : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have h3 : Valued.v ((((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)) =
      WithZero.exp (ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) := by
    rw [eq_inv_of_mul_eq_one_left h1, map_inv₀, GlobalTheory.BorelUMod.v_eq_exp h0, ← WithZero.exp_neg, neg_neg]
  have h4 : Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k).rev (lo k).rev) =
      WithZero.exp (ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) := by
    rw [← h3, h2, hσ]
  rw [map_mul, map_mul, h3, h4, two_mul, WithZero.exp_add, mul_right_comm]

theorem conj_mem_cellU_last [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q)
    {n : ℕ} {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n)
    {y : GU σ n} (hy : y ∈ KU σ n) (hw : IsWeylRep (simpleU k) (y : GL (Fin n) L))
    (t : GU σ n) (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0)
    (u : GU σ n) (hu : u ∈ cellU y) : t⁻¹ * u * t ∈ cellU y := by
  rw [mem_cellU_last_iff L ϖ σ q hU n k hk hn y hy hw] at hu ⊢
  obtain ⟨⟨hb, hd⟩, hz⟩ := hu
  have e := diag_mul_mul_diag_apply t⁻¹ u t (diag_inv_of_diag t ht) ht
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij h => ?_⟩
  · rw [e, hb i j hij, mul_zero, zero_mul]
  · rw [e, hd i, mul_one, diag_inv_mul_diag t ht]
  · rw [e, hz i j hij h, mul_zero, zero_mul]

theorem integral_conj_diag_cellU_last :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) * ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal, ∫⁻ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        ‖(q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)))‖ₑ * ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw _ _ μ _ hμ t ht
  have hsh := (GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hU n k hk hn y hy hw).1
  have hvol := GlobalTheory.T.haar_measure_weyl_cell_odd_unitary L ϖ σ q hU n k hk hn y hy hw μ hμ
  have hcv := v_cornerU_conj hU.2.1 k t ht
  have hq : (2 : ℕ) ≤ q := hU.2.2.2.2.2.1
  generalize ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)) = o at hcv ⊢
  have hm := conj_mem_cellU_last hU hk hn hy hw t ht
  have hm' := conj_mem_cellU_last hU hk hn hy hw t⁻¹ (diag_inv_of_diag t ht)
  let κ : cellU y ≃* cellU y :=
    { toFun := fun u => ⟨t⁻¹ * u * t, hm u u.2⟩
      invFun := fun u => ⟨t⁻¹⁻¹ * u * t⁻¹, hm' u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hc : Continuous κ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hc' : Continuous κ.symm := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let e : cellU y ≃ᵐ cellU y := (Homeomorph.mk κ.toEquiv hc hc').toMeasurableEquiv
  have he : ∀ u : cellU y, ((e u : cellU y) : GU σ n) = t⁻¹ * u * t := fun u => rfl
  haveI : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ κ hc hc'
  haveI : LocallyCompactSpace (cellU y) :=
    (hsh 0).2.1.locallyCompactSpace_of_mem_nhds_of_group ((hsh 0).1.mem_nhds (hsh 0).2.2.1)
  have hpre : ∀ j : ℤ, e ⁻¹' shellU k y j = shellU k y (j - 2 * o) := by
    intro j
    ext u
    simp only [Set.mem_preimage, shellU, Set.mem_setOf_eq, he, hcv]
    rw [WithZero.exp_sub, le_div_iff₀' (WithZero.exp_pos)]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hnorm : ‖(q : ℂ) ^ (-4 * o)‖ = (q : ℝ) ^ (-4 * o) := by
    rw [norm_zpow, Complex.norm_natCast]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = |o| := ⟨o.natAbs, by simp⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = a - o := ⟨(a - o).toNat, by
    rw [Int.toNat_of_nonneg]; rw [ha]; linarith [le_abs_self o]⟩
  have key : μ.map e = ‖(q : ℂ) ^ (-4 * o)‖ₑ • μ := by
    refine GlobalTheory.T.haarMeasure_unique_sigmaCompact_normalised_compactOpen (cellU y) μ (μ.map e) (fun j : ℕ => shellU k y j)
      (fun j => ⟨(hsh j).2.1, (hsh j).1.measurableSet⟩) ?_ (shellU k y ((2 * a : ℕ) : ℤ)) _ (hsh _).1 (hsh _).2.1
      ⟨1, (hsh _).2.2.1⟩ ?_
    · exact Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ⟨_, mem_shellU_depth k y u⟩
    · rw [e.map_apply, hpre]
      have h2 : ((2 * a : ℕ) : ℤ) - 2 * o = ((2 * b : ℕ) : ℤ) := by push_cast; rw [hb]; ring
      rw [h2, hvol, hvol, ← ofReal_norm_eq_enorm, hnorm, ← ENNReal.ofReal_natCast q,
        ← ENNReal.ofReal_pow (Nat.cast_nonneg q), ← ENNReal.ofReal_pow (Nat.cast_nonneg q),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0]
      congr 1
      have e1 : 2 * a / 2 = a := by omega
      have e2 : 2 * b / 2 = b := by omega
      rw [e1, e2]
      push_cast
      rw [hb]; ring
  refine ⟨fun F => ?_, fun F => ?_⟩
  · have h := integral_map_equiv (μ := μ) e (fun u : cellU y => F (u : GU σ n))
    rw [key, integral_smul_measure, toReal_enorm, hnorm, Complex.real_smul] at h
    simp only [he] at h
    rw [← h]
    push_cast
    rfl
  · have h := lintegral_map_equiv (μ := μ) (fun u : cellU y => F (u : GU σ n)) e
    rw [key, lintegral_smul_measure, smul_eq_mul] at h
    simp only [he] at h
    exact h.symm

end WeylUnipotentShell

end WeylCell

end GlobalTheory

end
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.WeylUnipotentShell.Atone

theorem level_sets {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℕ) (V : ℕ → ℝ)
    (hmeas : ∀ j : ℕ, MeasurableSet {x | f x ≤ j})
    (hV : ∀ j, μ {x | f x ≤ j} = ENNReal.ofReal (V j))
    (hV0 : ∀ j, 0 ≤ V j) :
    Measurable f ∧ ∀ j, μ (f ⁻¹' {j}) = ENNReal.ofReal (V j - if j = 0 then 0 else V (j - 1)) := by
  have hset : ∀ i : ℕ, f ⁻¹' {i + 1} = {x | f x ≤ i + 1} \ {x | f x ≤ i} := by
    intro i; ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]; omega
  have hset0 : f ⁻¹' {0} = {x | f x ≤ 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]; omega
  refine ⟨measurable_to_countable' fun j => ?_, fun j => ?_⟩
  · rcases j with _ | i
    · rw [hset0]; exact hmeas 0
    · rw [hset]; exact (hmeas _).diff (hmeas _)
  · rcases j with _ | i
    · rw [hset0, hV]; simp
    · have hsub : {x | f x ≤ i} ⊆ {x | f x ≤ i + 1} := fun x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢; omega
      rw [hset, measure_diff hsub (hmeas i).nullMeasurableSet (by rw [hV]; exact ENNReal.ofReal_ne_top),
        hV, hV, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, ENNReal.ofReal_sub _ (hV0 i)]

theorem sums_over_levels {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℕ) (hf : Measurable f)
    (w : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : ∀ j, μ (f ⁻¹' {j}) = ENNReal.ofReal (w j))
    (c : ℕ → ℂ) (s : ℂ) (hs : HasSum (fun j => c j * (w j : ℂ)) s) (r : ℝ)
    (hr : HasSum (fun j => ‖c j‖ * w j) r) :
    ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r ∧ Integrable (fun x => c (f x)) μ ∧ ∫ x, c (f x) ∂μ = s := by
  have hmap : ∀ j, (μ.map f) {j} = ENNReal.ofReal (w j) := fun j => by
    rw [Measure.map_apply hf (measurableSet_singleton j)]; exact hw j
  have hL : ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r := by
    rw [← lintegral_map (f := fun j => ‖c j‖ₑ) measurable_from_nat hf, lintegral_countable']
    simp_rw [hmap]
    rw [← hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (norm_nonneg _) (hw0 j)) hr.summable]
    congr 1; funext j
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
  have hI : Integrable (fun x => c (f x)) μ := by
    refine ⟨(measurable_from_nat.comp hf).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL]; exact ENNReal.ofReal_lt_top
  refine ⟨hL, hI, ?_⟩
  have hIm : Integrable c (μ.map f) :=
    (integrable_map_measure measurable_from_nat.aestronglyMeasurable hf.aemeasurable).2 hI
  rw [← integral_map hf.aemeasurable measurable_from_nat.aestronglyMeasurable, integral_countable hIm,
    ← hs.tsum_eq]
  congr 1; funext j
  rw [measureReal_def, hmap, ENNReal.toReal_ofReal (hw0 j), Complex.real_smul, mul_comm]

end GlobalTheory.WeylCell.WeylUnipotentShell.Atone


open GlobalTheory.WeylCell.WeylUnipotentShell.Atone in
theorem _root_.GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ z : ℂ, ‖z‖ < 1 →
      Integrable (fun u : cellU y => (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)) μ ∧
      ∫ u : cellU y, (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) ∂μ = cSU q z ∧
      ∫⁻ u : cellU y, ‖(z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)‖ₑ ∂μ = ‖cSU q ((‖z‖ : ℝ) : ℂ)‖ₑ := by
  intro L _ _ _ ϖ σ q hq n k hk hn y hy hwy _ _ μ _ hμ z hz
  have q2 : 2 ≤ q := hq.2.2.2.2.2.1
  have hsh := GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hq n k hk hn y hy hwy
  have hvol := GlobalTheory.T.haar_measure_weyl_cell_odd_unitary L ϖ σ q hq n k hk hn y hy hwy μ hμ
  let f : cellU y → ℕ := fun u => depthU k (u : GU σ n)
  let V : ℕ → ℝ := fun j => (q : ℝ) ^ (j + 2 * (j / 2))
  have hV0 : ∀ j, 0 ≤ V j := fun j => by positivity
  have hlev : ∀ j : ℕ, {u : cellU y | f u ≤ j} = shellU k y j := by
    intro j; ext u; exact (mem_shellU_iff_depth k y j u).symm
  have hmeas : ∀ j : ℕ, MeasurableSet {u : cellU y | f u ≤ j} := fun j => by
    rw [hlev]; exact (hsh.1 j).1.measurableSet
  have hV : ∀ j : ℕ, μ {u : cellU y | f u ≤ j} = ENNReal.ofReal (V j) := fun j => by
    rw [hlev, hvol j, ENNReal.ofReal_pow (Nat.cast_nonneg q), ENNReal.ofReal_natCast]
  obtain ⟨hf, hlv⟩ := level_sets μ f V hmeas hV hV0
  let w : ℕ → ℝ := fun j => V j - if j = 0 then 0 else V (j - 1)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hw0 : ∀ j, 0 ≤ w j := fun j => by
    simp only [w, V]
    split_ifs with h
    · simp only [sub_zero]; positivity
    · rw [sub_nonneg]; exact pow_le_pow_right₀ hq1 (by omega)
  have hwc : ∀ j : ℕ, ((w j : ℝ) : ℂ) = (q : ℂ) ^ (j + 2 * (j / 2)) -
      (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))) := fun j => by
    simp only [w, V]; split_ifs <;> push_cast <;> rfl
  let c : ℕ → ℂ := fun j => (z / (q : ℂ) ^ 2) ^ j
  have hs : HasSum (fun j => c j * (w j : ℂ)) (cSU q z) := by
    simp only [c, hwc]; exact GlobalTheory.T.hasSum_cSU_power_differences q q2 z hz
  have hz' : ‖((‖z‖ : ℝ) : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hz
  have hs' := GlobalTheory.T.hasSum_cSU_power_differences q q2 _ hz'
  have hterm : ∀ j : ℕ, (((‖z‖ : ℝ) : ℂ) / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2)))) =
      ((‖c j‖ * w j : ℝ) : ℂ) := fun j => by
    rw [← hwc]; simp only [c, norm_pow, norm_div, Complex.norm_natCast]; push_cast; rfl
  simp only [hterm] at hs'
  have hsum : Summable (fun j => ‖c j‖ * w j) := Complex.summable_ofReal.1 hs'.summable
  have hr := hsum.hasSum
  have heq : cSU q ((‖z‖ : ℝ) : ℂ) = ((∑' j, ‖c j‖ * w j : ℝ) : ℂ) :=
    hs'.unique (Complex.hasSum_ofReal.2 hr)
  obtain ⟨h1, h2, h3⟩ := sums_over_levels μ f hf w hw0 hlv c _ hs _ hr
  refine ⟨h2, h3, ?_⟩
  rw [h1, heq, ← ofReal_norm_eq_enorm, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (hw0 j))]
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_unitary_matrix_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c x : GL (Fin d) (Fv F v)),
    ∃ h ∈ UAt σ W (evFin F v), locMat t c h = x := by
  first | exact @GlobalTheory.SkewSplitSurj.exists_locMat_eq | exact GlobalTheory.SkewSplitSurj.exists_locMat_eq | (intros; apply GlobalTheory.SkewSplitSurj.exists_locMat_eq <;> assumption)
end

section

open scoped SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.ArchUniq

open GlobalTheory.RealWeil

theorem pairingCoords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland

theorem symplMatrix : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm

end GlobalTheory.ArchUniq

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

end GlobalTheory.ArchUniq
end
end
