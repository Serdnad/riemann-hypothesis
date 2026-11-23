module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnePowNotMemHeightOneAsIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle455
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle457
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle401
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RealType
open GlobalTheory.AutMult (toFin toInf)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopIntegral

theorem isBlock_unique {R : Type} [Zero R] {N n : ℕ} {hN : N = n + 1} {A' B' : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} {t : R} (h : GlobalTheory.BranchFormula.IsBlock hN A' A t) (h' : GlobalTheory.BranchFormula.IsBlock hN B' A t) :
    A' = B' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have cover : ∀ i : Fin N, (∃ a : Fin n, i = Formalism.L2.Col.Br.iC hN a) ∨ i = Formalism.L2.Col.Br.iL hN := by
    intro i
    by_cases hi : i.val < n
    · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · right
      apply Fin.ext
      show i.val = n
      have := i.isLt
      omega
  ext i j
  rcases cover i with ⟨a, rfl⟩ | rfl <;> rcases cover j with ⟨b, rfl⟩ | rfl
  · rw [h1, h1']
  · rw [(h2 a).1, (h2' a).1]
  · rw [(h2 b).2, (h2' b).2]
  · rw [h3, h3']

theorem exists_avg_form {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H]
    [BorelSpace H] (κ : Measure H) [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (ρ : H →* Module.End ℂ A) (ρ' : H →* Module.End ℂ B) (Λ : Module.Dual ℂ A)
    (Λ' : Module.Dual ℂ B) (hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) :
    ∃ β : A →ₗ[ℂ] B →ₗ[ℂ] ℂ, (∀ v v', β v v' = ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ∧
      ∀ k v v', β (ρ k v) (ρ' k v') = β v v' := by
  have hint : ∀ v v', Integrable (fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) κ := fun v v' =>
    (hc v v').integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  refine ⟨LinearMap.mk₂ ℂ (fun v v' => ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ?_ ?_ ?_ ?_, fun v v' => rfl, ?_⟩
  · intro v₁ v₂ v'
    simp only [map_add (f := _), add_mul]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro v v₁ v₂
    simp only [map_add (f := _), mul_add]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro k v v'
    simp only [LinearMap.mk₂_apply]
    have e : ∀ j : H, Λ (ρ j⁻¹ (ρ k v)) * Λ' (ρ' j⁻¹ (ρ' k v')) =
        (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) (k⁻¹ * j) := by
      intro j
      simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    simp_rw [e]
    exact integral_mul_left_eq_self (μ := κ) (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) k⁻¹

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

theorem exists_orthogonal_summand_embedding_hom {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) :
    ∃ s : GA D A →* GA D B, Continuous s ∧ (∀ h, stabilizerEmbedding d h = s h) ∧ ∀ γ ∈ GQ A, s γ ∈ GQ B := by
  obtain ⟨s, hs, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A d.ι d.isom
  refine ⟨s, hs, fun h => ?_, hrat⟩
  exact ((hrel h _).1 ((embRel_iff d h _).2 rfl))


variable (G) in
theorem isV_last : (G.node (.grid D.R.m D.R.m)).IsV (rankV D D.R.m D.R.m) 0 := by
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by
    intro j hj
    injection hj with h1 h2
    have := D.R.two_le_m
    omega)
  simpa [Node.neg, Node.rank] using h


variable (G) in
theorem isDefinite_last : IsDefiniteSpace (G.V (.grid D.R.m D.R.m)) := GlobalTheory.RowClaim.TermVolDef.isDefiniteSpace_of_isV (isV_last G)


variable (G) in
theorem one_le_rank_last : 1 ≤ (G.V (.grid D.R.m D.R.m)).rank := by
  rw [(isV_last G).rank, rankV, sLen]
  have := D.R.two_le_m
  nlinarith
private theorem isBlock_embGL' {n N : ℕ} (hN : N = n + 1) (g : GL (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ)
      (g : Matrix (Fin n) (Fin n) ℂ) 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_left ⟨a.2, b.2⟩]
    rfl
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.2 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h))]
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.1 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h).symm)]
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]

variable {θ : InfFam D} (hθ : IsInfFam θ) (N : Std G U)
include hθ

theorem exists_real_point (u : D.what₂.Tau → Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) :
    ∃ k : GinfC (G.V (.grid D.R.m D.R.m)),
      rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k) = rhoK (wt G (.top D.R.m)) (GlobalTheory.BrUnique.diagU G.sp.topDec.rank.symm u) ∧
      rhoAt θ N (.grid D.R.m D.R.m) k = rhoK (wt G (.grid D.R.m D.R.m)) (GlobalTheory.BrUnique.uGL u) := by
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hu : ∀ τ, (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) ∈
      Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ := by
    intro τ
    have e1 : (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) =
        (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose := rfl
    have h1 : (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) *
        star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (u τ).2
    rw [e1, Matrix.mem_unitaryGroup_iff]
    have h2 : star (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose =
        (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ).transpose := by
      ext i j
      simp [Matrix.star_apply]
    rw [h2, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  obtain ⟨k, hk⟩ := GlobalTheory.RealType.exists_realAt_eq (hθ := hθ) (N := N) hX (invTrK (GlobalTheory.BrUnique.uGL u)) hu
  refine ⟨k, ?_, ?_⟩
  · rw [GlobalTheory.RealType.rhoAt_apply]
    refine congrArg (rhoK (wt G (.top D.R.m))) (funext fun τ => Units.ext ?_)
    have hb := GlobalTheory.RealType.isBlock_invTrK_realAt hθ N (k : GA D (G.V (.grid D.R.m D.R.m))) τ
    rw [hk, GlobalTheory.BrUnique.invTrK_invTrK] at hb
    exact isBlock_unique hb (isBlock_embGL' _ _)
  · rw [GlobalTheory.RealType.rhoAt_apply, hk, GlobalTheory.BrUnique.invTrK_invTrK]

theorem continuous_integrand (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (v : VV ℂ (wt G (.top D.R.m)))
    (v' : VV ℂ (wt G (.grid D.R.m D.R.m))) : Continuous fun h : GA D (G.V (.grid D.R.m D.R.m)) =>
      Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec h)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) h⁻¹ v') := by
  obtain ⟨s, hs, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  simp_rw [he]
  exact ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ) v).comp hs.inv).mul
    ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ') v').comp continuous_inv)

theorem real_average (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (κ : Measure (GinfC (G.V (.grid D.R.m D.R.m))))
    [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] :
    ∃ c : ℂ, ∀ (v : VV ℂ (wt G (.top D.R.m))) (v' : VV ℂ (wt G (.grid D.R.m D.R.m))),
      ∫ k, Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) (k : GA D _)⁻¹ v') ∂κ =
        c * brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) v v' := by
  have hV := isDefinite_last G
  have : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) :=
    isCompact_iff_compactSpace.mp (Formalism.IndefR.Eqv.isCompact_GinfC hV.1 hV.2)
  obtain ⟨s, -, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  let ρ : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.top D.R.m))) :=
    (rhoAt θ N (.top D.R.m)).comp (s.comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype)
  let ρ' : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.grid D.R.m D.R.m))) :=
    (rhoAt θ N (.grid D.R.m D.R.m)).comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype
  have e1 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m)))) := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, he]
  have e1' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k⁻¹ = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m))))⁻¹ := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_inv, he]
  have e2 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m))) := fun k => rfl
  have e2' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k⁻¹ = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m)))⁻¹ := fun k => rfl
  have hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') := by
    intro v v'
    simp_rw [e1', e2']
    exact (continuous_integrand hθ N Λ Λ' v v').comp continuous_subtype_val
  obtain ⟨β, hβ, hinv⟩ := exists_avg_form κ ρ ρ' Λ Λ' hc
  obtain ⟨c, hc'⟩ := GlobalTheory.BrUnique.brPair_unique G.sp.topDec.rank.symm (one_le_rank_last G)
    (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).1) (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).2) β (by
      intro u v f
      obtain ⟨k, hk1, hk2⟩ := exists_real_point hθ N u
      have h := hinv k v f
      rw [e1, e2, hk1, hk2] at h
      exact h)
  refine ⟨c, fun v v' => ?_⟩
  have h := hβ v v'
  simp_rw [e1', e2'] at h
  rw [← h]
  exact (DFunLike.congr_fun (DFunLike.congr_fun hc' v) v').trans rfl

end GlobalTheory.TopIntegral

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

noncomputable section

theorem GlobalTheory.RowEx.dat_choice_exists : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  classical
  intro hE
  obtain ⟨CF0, hE⟩ := hE
  refine ⟨CF0, fun CF hCF => ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩⟩
  obtain ⟨x₀, hx⟩ := hE eps CF hCF
  refine ⟨x₀, fun K _ _ _ hK hxK => ?_⟩
  have hF := hx K.s hK hxK
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if h : Ξ.Finite then Classical.choose (hF P f Ξ h) else ∅, by simp, ?_, ?_⟩
  · intro P f _ _ Ξ z hz
    by_cases h : Ξ.Finite
    · dsimp only at hz
      rw [dite_eq_left h] at hz
      exact (Classical.choose_spec (hF P f Ξ h)).1 z hz
    · dsimp only at hz
      rw [dite_eq_right h] at hz
      simp at hz
  · intro B f T _ hH _ _ w Z hX Wt z L hL hS
    obtain ⟨hq, hC, hfin, hmem⟩ := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z hX Wt z
    have hS2 := hH.2
    dsimp only at hS2
    rw [dite_eq_left hfin] at hS2
    rw [hL]
    exact (Classical.choose_spec (hF B.toPre f (T.set f) hfin)).2 (w.st Z) f rfl HEq.rfl L hL _ _ _ _ _ _ _ hS hC hq
      (fun t => ⟨_, hmem t, HEq.rfl⟩) (fun y hy => hS2 y hy)

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.fourier_uniqueness_realComponents_adelicHom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ x : Y → Mx D W.rank ρ, Measurable x → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → ∫ y, ψ (symplO V W (d.extX W (x y)) (d.extY W c)) * F y ∂m = 0) → ∀ S : Set (Mx D W.rank ρ), MeasurableSet S → (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) → ∫ y in x ⁻¹' S, F y ∂m = 0 := by
  first | exact @GlobalTheory.FourierRealPart.integral_preimage_eq_zero | exact GlobalTheory.FourierRealPart.integral_preimage_eq_zero | (intros; apply GlobalTheory.FourierRealPart.integral_preimage_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareComm.LineDeriv

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

private theorem hD_eq_mul_add_fderiv {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (w : G)
    (hf : DifferentiableAt ℝ (fun x : R => f (w + ι x)) 0) (u : R) :
    hD ι π om u f w =
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u := by
  have hlin : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hF : HasDerivAt (fun t : ℝ => f (w + ι (t • u))) (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
    have h0 : ((0 : ℝ) • u) = 0 := zero_smul ℝ u
    have hf' : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u) := by rwa [h0]
    have := hf'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hlin
    rw [h0] at this
    exact this
  have hP : HasDerivAt (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ)))
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) 0 := by
    have e : (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ))) =
        fun t : ℝ => Complex.exp ((t : ℂ) * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ))) := by
      funext t
      rw [map_smul, smul_eq_mul]
      push_cast
      ring_nf
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)))
        (1 * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ))) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const _
    simpa using h1.cexp
  have hPF := hP.mul hF
  unfold hD
  exact hPF.deriv.trans (by simp)

theorem dLine_eq_sum_dRho {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO S T} (hL : IsRealDir T S L) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ τ, Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  classical
  obtain ⟨σ, hσ⟩ := exists_chart hθ
  funext w
  have hd : DifferentiableAt ℝ (fun x => f (w + iotaW σ T S x)) 0 :=
    ((theta_sm hσ hf w).differentiable (by simp)).differentiableAt
  rw [Finset.sum_apply, dLine_eq_hD hσ hψ hL f, hD_eq_mul_add_fderiv _ _ _ _ _ hd]
  have hτ : ∀ τ, Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f w =
      (-(Real.pi * Complex.I) * ((omO S T (piW θ T S w) (Pi.single τ (compAt θ τ (L 1))) : ℝ) : ℂ)) * f w +
        fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (Pi.single τ (compAt θ τ (L 1))) := by
    intro τ
    rw [dRho_eq_dLine, dLine_eq_hD hσ hψ (isRealDir_lineAt hθ τ _) f, GlobalTheory.FockIndep.piW_lineAt hθ τ]
    exact hD_eq_mul_add_fderiv _ _ _ _ _ hd _
  rw [Finset.sum_congr rfl fun τ _ => hτ τ, Finset.sum_add_distrib]
  have hp : piW θ T S (L 1) = ∑ τ, (Pi.single τ (compAt θ τ (L 1)) : RW T S) := by
    exact (Finset.univ_sum_single (piW θ T S (L 1))).symm

  rw [hp, map_sum, map_sum]
  simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]

theorem deriv_line_mem_algF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X), ∀ Φ ∈ algF ψ θ ε A B,
      ∀ L : ℝ →+ WO (sgn ε M) X, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
        (fun x => deriv (fun t : ℝ => heisO ψ (sgn ε M) X (L t) Φ x) 0) ∈ algF ψ θ ε A B := by
  intro D ψ θ hψ hθ ε M X A B Φ hΦ L hLc hLf
  have hsub : algF ψ θ ε A B ≤ GlobalTheory.RealWeil.thetaSub ψ (sgn ε M) X := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, P, hg, rfl⟩
    have hg' : IsThetaFunO ψ (sgn ε M) X g := hg.1
    show IsThetaFunO ψ (sgn ε M) X (fockF ψ θ ε A B g P)
    unfold fockF pureTensorO aPlusAll
    exact GlobalTheory.FockIndep.pure_mem (fun _ _ h h' => GlobalTheory.OrientedHeis.theta_add h h')
      (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
      (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) hg' P
  have hth : IsThetaFunO ψ (sgn ε M) X Φ := hsub hΦ
  have hL : IsRealDir X (sgn ε M) L := ⟨hLc, hLf⟩
  show dLine ψ (sgn ε M) X L Φ ∈ algF ψ θ ε A B
  rw [dLine_eq_sum_dRho hψ hθ hL hth]
  exact Submodule.sum_mem _ fun τ _ => GlobalTheory.SquareComm.dRho_mem_algF D ψ θ hψ hθ ε M X A B Φ hΦ τ _

end GlobalTheory.SquareComm.LineDeriv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TripleRam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_nonSplitAt_of_emb {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ¬ GlobalTheory.WeilParts.NonSplitAt D v ε := by
  intro h
  refine h.2 ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
  have he : ε = GlobalTheory.EmbChart.atPlace v 1 := by
    obtain ⟨α, rfl, h1, h0⟩ := hε
    rw [GlobalTheory.EmbChart.atPlace_apply]
    congr 1
    refine FiniteAdeleRing.ext _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
    by_cases e : u = v
    · subst e; rw [GlobalTheory.AdelicU.evalV_singleFin_self, h1]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, h0 u e]
  rw [he, GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl

theorem not_unramAt_of_forall {D : D7} {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → ¬ GlobalTheory.LFun.UnrAt χ w) :
    ¬ GlobalTheory.WeilParts.UnramAt ε χ := by
  intro hu
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hl.over.symm
  exact h w hw (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D χ v ε hε hu w hw)

theorem ram_clause : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ (M : Vol G), M.Is t → ∀ (en : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G ↑i ↑j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G ↑i ↑j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) om om',
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t ↑i ↑j en Bs Γ X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j) ∧ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j)) ∨
      (¬ GlobalTheory.WeilParts.NonSplitAt D v ε ∧ ¬ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j) ∧
        ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  intro D T L sc G μ₀ hL W t i j hS M hM en Bs Γ X om om' hX hT v ε hε
  by_cases hv : v ∈ X.T
  · right
    have hP : v ∈ Bs.P := hT.chars.sub hv
    refine ⟨not_nonSplitAt_of_emb hε (Bs.τ ⟨v, hP⟩), ?_, GlobalTheory.T.not_dvd_differentIdeal_of_standardAddChar_unramified hT.base.std (hT.base.psiP v hP)⟩
    rw [← hX.α, ← hX.β]
    exact not_unramAt_of_forall hε fun w hw => hT.chars.ram w (hw ▸ hv)
  · left
    rw [← hX.α, ← hX.β]
    exact ⟨GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_unramified_over_place hε fun w hw => hT.chars.unrα w (fun h => hv (hw ▸ h)),
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_unramified_over_place hε fun w hw => hT.chars.unrβ w (fun h => hv (hw ▸ h))⟩

end GlobalTheory.TripleRam

end
end
