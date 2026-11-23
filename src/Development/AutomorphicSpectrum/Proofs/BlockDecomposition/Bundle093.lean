module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle069
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle071
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace

@[expose] public section

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL

variable (K : Type) [Field K]

theorem sum_fin_of_ge_zero {d j : ℕ} (hjd : j ≤ d) (f : Fin d → K)
    (hf : ∀ k : Fin d, j ≤ (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k : Fin j, f (Fin.castLE hjd k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjd
  rw [Fin.sum_univ_add]
  have h0 : ∑ k : Fin m, f (Fin.natAdd j k) = 0 :=
    Finset.sum_eq_zero fun k _ => hf _ (by simp)
  rw [h0, add_zero]
  rfl

theorem blkEmb_row_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : j ≤ (i : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dite_eq_right fun h => (not_lt.2 hi) h.1]

theorem blkEmb_col_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hl : j ≤ (l : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dite_eq_right fun h => (not_lt.2 hl) h.2]

theorem blkEmb_lt {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : (i : ℕ) < j) (hl : (l : ℕ) < j) :
    blkEmb K d j A i l = A ⟨i, hi⟩ ⟨l, hl⟩ := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dite_eq_left ⟨hi, hl⟩]

theorem blkEmb_one (d j : ℕ) : blkEmb K d j (1 : Matrix (Fin j) (Fin j) K) = 1 := by
  ext i l
  rw [Matrix.one_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.one_apply]
      simp [Fin.ext_iff]
    · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l (not_lt.1 hl)
  · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l (not_lt.1 hi)

theorem blkEmb_mul {d j : ℕ} (hjd : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) :
    blkEmb K d j (A * B) = blkEmb K d j A * blkEmb K d j B := by
  ext i l
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.mul_apply,
        GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.sum_fin_of_ge_zero K hjd]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hk : ((Fin.castLE hjd k : Fin d) : ℕ) < j := k.2
        rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i _ hi hk,
          GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ _ l hk hl]
        rfl
      · intro k hk
        rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i k hk, if_neg (by rintro rfl; omega),
          zero_mul]
    · have hl' : j ≤ (l : ℕ) := not_lt.1 hl
      rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l hl']
      simp only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K B _ l hl', mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K A i l hl']
  · have hi' : j ≤ (i : ℕ) := not_lt.1 hi
    rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l hi']
    simp only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K A i _ hi', ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K B i l hi']

theorem exists_gl_blkEmb : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d →
    ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  intro K _ _ _ d j hjd g
  refine ⟨⟨GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j (g : Matrix (Fin j) (Fin j) K),
    GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K), ?_, ?_⟩, rfl, rfl⟩
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]

end GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

theorem delta_ne_zero (c : Matrix (Fin m) (Fin m) K) : delta c ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (Finset.univ : Finset (Fin m × Fin m)) (fun p => c p.1 p.2)
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose r hr using fun (i j : Fin m) => RingHom.mem_rangeS.1 (hb (i, j) (Finset.mem_univ _))
  have hr' : ∀ i j, algebraMap (𝓞 K) K (r i j) = algebraMap (𝓞 K) K (b : 𝓞 K) * c i j := by
    intro i j
    rw [hr i j, Algebra.smul_def]
  let I : Ideal (𝓞 K) := Ideal.span {(b : 𝓞 K)}
  have hI : I ≠ ⊥ := fun h => hb0 (Ideal.span_singleton_eq_bot.1 h)
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let π : (Fin m → 𝓞 K) →+ (Fin m → 𝓞 K ⧸ I) :=
    AddMonoidHom.pi (fun i => (Ideal.Quotient.mk I).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hker : π.ker ≤ Kc c := by
    intro y hy
    have h0 : π y = 0 := AddMonoidHom.mem_ker.1 hy
    have hyI : ∀ j, y j ∈ I := fun j =>
      Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h0 j)
    choose z hz using fun j => Ideal.mem_span_singleton'.1 (hyI j)
    change ∀ i : Fin m, ∃ o : 𝓞 K,
      algebraMap (𝓞 K) K o = c.mulVec (fun j => algebraMap (𝓞 K) K (y j)) i
    intro i
    refine ⟨∑ j, r i j * z j, ?_⟩

    rw [map_sum]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, hr' i j, ← hz j, map_mul]
    ring
  have hfin : (π.ker).index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  exact ne_zero_of_dvd_ne_zero hfin (AddSubgroup.index_dvd_of_le hker)

theorem delta_eq_relIndex (c : Matrix (Fin m) (Fin m) K) :
    delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  classical
  let L := (lam c).toAddSubgroup
  let H : AddSubgroup L := (intVec K m).toAddSubgroup.addSubgroupOf L
  let f0 : (Fin m → 𝓞 K) →+ (Fin m → K) :=
    (c.mulVecLin.toAddMonoidHom).comp (AddMonoidHom.pi fun i =>
      (algebraMap (𝓞 K) K).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hmap : ∀ y, f0 y ∈ L := by
    intro y
    have : f0 y ∈ lam c := by
      unfold lam
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨fun j => algebraMap (𝓞 K) K (y j),
        fun j => ⟨y j, rfl⟩, rfl⟩)
    exact this
  let ψ : (Fin m → 𝓞 K) →+ L := f0.codRestrict L hmap
  let φ : (Fin m → 𝓞 K) →+ L ⧸ H := (QuotientAddGroup.mk' H).comp ψ
  have hker : Kc c = φ.ker := by
    ext y
    rw [AddMonoidHom.mem_ker]
    change _ ↔ (QuotientAddGroup.mk (ψ y) : L ⧸ H) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      have hx' : x ∈ lam c := hx
      unfold lam at hx'
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      choose y hy using hv
      refine ⟨y, ?_⟩
      have hyv : (fun j => algebraMap (𝓞 K) K (y j)) = v := funext hy
      change (QuotientAddGroup.mk (ψ y) : L ⧸ H) = QuotientAddGroup.mk _
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have key : ((-(ψ y) + ⟨_, hx⟩ : L) : Fin m → K) = a := by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_neg]
        change -(c.mulVec (fun j => algebraMap (𝓞 K) K (y j))) + (a + c.mulVec v) = a
        rw [hyv]
        abel
      rw [key]
      exact ha
  show (Kc c).index = H.index
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
  rfl

theorem delta_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K),
    delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  intro K _ _ m c
  exact ⟨delta_ne_zero c, delta_eq_relIndex c⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex
end
end

section

open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

theorem asAlgebraHom_centralIdem {Γ V W : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) :
    σ.asAlgebraHom (centralIdem ρ) =
      ∑ g, ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) • σ g := by
  unfold centralIdem

  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => Representation.asAlgebraHom_single _ _ _

theorem centralIdemAct : ReciprocityTheory.Ty.Fin.St.CentralIdemAct := by
  intro Γ _ _ V _ _ _ W _ _ _ ρ σ hρ hσ
  obtain ⟨hVn, hρ'⟩ := hρ
  obtain ⟨hWn, hσ'⟩ := hσ
  haveI := hVn
  haveI := hWn
  haveI hirrρ : ρ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of ρ hρ'
  haveI hirrσ : σ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of σ hσ'
  have hc0 : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Nat.card Γ : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hV0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hW0 : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  obtain ⟨μ, hμ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.schur_scalar σ hσ'
    (fun g => (Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) (by
      intro g k
      have e : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
      have := Representation.char_conj ρ g⁻¹ k
      simp only [Representation.character] at this
      simp only [e, this])
  have hT : σ.asAlgebraHom (centralIdem ρ) = μ • (1 : Module.End ℂ W) := by
    rw [asAlgebraHom_centralIdem]; exact hμ
  have htr : μ * (Module.finrank ℂ W : ℂ) = (Module.finrank ℂ V : ℂ) *
      ((Nat.card Γ : ℂ)⁻¹ * ∑ g, σ.character g * ρ.character g⁻¹) := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ

    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum, Finset.mul_sum, Nat.card_eq_fintype_card]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Representation.character]
    field_simp
  rw [Representation.char_orthonormal σ ρ] at htr
  rw [hT]
  by_cases h : Nonempty (Representation.Equiv ρ σ)
  · rw [if_pos h] at htr ⊢
    obtain ⟨φ⟩ := h
    have hd : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    rw [hd] at htr
    have : μ = 1 := by
      apply mul_right_cancel₀ hW0
      simpa using htr
    rw [this, one_smul]
  · rw [if_neg h] at htr ⊢
    have : μ = 0 := by
      have h0 : μ * (Module.finrank ℂ W : ℂ) = 0 := by simpa using htr
      exact (mul_eq_zero.mp h0).resolve_right hW0
    rw [this, zero_smul]

end GlobalTheory.CompanionTheory.TyFin
end

section

open CategoryTheory ReciprocityTheory.Ty.Fin PI.GreenHCLabel

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin

theorem nonempty_iso_iff_intertwiner {Γ : Type} [Group Γ] (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v) := by
  constructor
  · rintro ⟨i⟩
    refine ⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩
    rw [FDRep.Iso.conj_ρ i γ, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨e, he⟩
    have h1 : ∀ g, e.toLinearMap ∘ₗ τ.ρ g = σ.ρ g ∘ₗ e.toLinearMap :=
      fun g => LinearMap.ext fun v => he g v
    have h2 : ∀ g, e.symm.toLinearMap ∘ₗ σ.ρ g = τ.ρ g ∘ₗ e.symm.toLinearMap := by
      intro g
      refine LinearMap.ext fun v => ?_
      show e.symm (σ.ρ g v) = τ.ρ g (e.symm v)
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    refine ⟨{ hom := basicsMk e.toLinearMap h1
              inv := basicsMk e.symm.toLinearMap h2
              hom_inv_id := ?_
              inv_hom_id := ?_ }⟩
    · ext v
      simp [basicsMk]
    · ext v
      simp [basicsMk]

private theorem simple_iff_isIrr {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) :
    CategoryTheory.Simple τ ↔ ReciprocityTheory.Ty.Fin.IsIrr τ.ρ := by
  constructor
  · intro hs
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      apply Simple.not_isZero τ
      rw [Limits.IsZero.iff_id_eq_zero]
      apply basics_hom_ext
      rw [basics_lin_id, basics_lin_zero]
      refine LinearMap.ext fun v => ?_
      exact @Subsingleton.elim _ hnt _ _
    · haveI hmono : Mono (basicsIncl τ W hW) :=
        basics_mono_of_inj _ (fun x y hxy => Subtype.ext hxy)
      rcases eq_or_ne (basicsIncl τ W hW) 0 with h0 | h0
      · left
        rw [Submodule.eq_bot_iff]
        intro w hw
        have h1 : basicsLin (basicsIncl τ W hW) (⟨w, hw⟩ : W) = w := rfl
        have h2 := congrArg (fun f => basicsLin f (⟨w, hw⟩ : W)) h0
        simp only [basics_lin_zero, LinearMap.zero_apply] at h2
        rw [← h1]
        exact h2
      · right
        haveI hiso : IsIso (basicsIncl τ W hW) :=
          (Simple.mono_isIso_iff_nonzero (basicsIncl τ W hW)).mpr h0
        rw [eq_top_iff]
        intro v _
        have h3 : basicsLin (inv (basicsIncl τ W hW) ≫ basicsIncl τ W hW) v = v := by
          rw [IsIso.inv_hom_id, basics_lin_id]
          rfl
        rw [basics_lin_comp] at h3
        rw [← h3]
        exact (basicsLin (inv (basicsIncl τ W hW)) v).2
  · rintro ⟨hnt, hirr⟩
    refine ⟨fun {Y} f hf => ⟨fun hiso h0 => ?_, fun h0 => ?_⟩⟩
    · subst h0
      have h1 : 𝟙 τ = 0 := by
        rw [← IsIso.inv_hom_id (0 : Y ⟶ τ), Limits.comp_zero]
      have h2 : basicsLin (𝟙 τ) = 0 := by
        rw [h1, basics_lin_zero]
      rw [basics_lin_id] at h2
      obtain ⟨⟨x, y, hxy⟩⟩ := hnt
      apply hxy
      have hx := LinearMap.congr_fun h2 x
      have hy := LinearMap.congr_fun h2 y
      simp only [LinearMap.id_apply, LinearMap.zero_apply] at hx hy
      rw [hx, hy]
    · have hinj := basics_inj_of_mono f
      have hinv : ∀ g : Γ, ∀ v ∈ LinearMap.range (basicsLin f),
          τ.ρ g v ∈ LinearMap.range (basicsLin f) := by
        rintro g v ⟨y, rfl⟩
        refine ⟨Y.ρ g y, ?_⟩
        exact LinearMap.congr_fun (basics_lin_comm f g) y
      rcases hirr _ hinv with hbot | htop
      · exfalso
        apply h0
        apply basics_hom_ext
        rw [basics_lin_zero]
        exact LinearMap.range_eq_bot.mp hbot
      · have hsurj : Function.Surjective (basicsLin f) := LinearMap.range_eq_top.mp htop
        let e := LinearEquiv.ofBijective (basicsLin f) ⟨hinj, hsurj⟩
        have hcomm : ∀ g : Γ, e.symm.toLinearMap ∘ₗ τ.ρ g = Y.ρ g ∘ₗ e.symm.toLinearMap := by
          intro g
          refine LinearMap.ext fun v => ?_
          show e.symm (τ.ρ g v) = Y.ρ g (e.symm v)
          apply e.injective
          rw [LinearEquiv.apply_symm_apply]
          show τ.ρ g v = basicsLin f (Y.ρ g (e.symm v))
          rw [← LinearMap.comp_apply (basicsLin f), basics_lin_comm f g, LinearMap.comp_apply]
          congr 1
          exact (e.apply_symm_apply v).symm
        refine ⟨⟨basicsMk e.symm.toLinearMap hcomm, ?_, ?_⟩⟩
        · apply basics_hom_ext
          rw [basics_lin_comp, basics_lin_id]
          refine LinearMap.ext fun y => ?_
          exact e.symm_apply_apply y
        · apply basics_hom_ext
          rw [basics_lin_comp, basics_lin_id]
          refine LinearMap.ext fun v => ?_
          exact e.apply_symm_apply v

theorem simpleIffIrr : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  unfold ReciprocityTheory.Ty.Fin.St.SimpleIffIrr
  exact ⟨fun Γ _ _ τ => simple_iff_isIrr τ, fun Γ _ _ τ σ => nonempty_iso_iff_intertwiner τ σ⟩

end GlobalTheory.CompanionTheory.TyFin
end
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.idempotent_localization_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime → (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧ (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := by
  first | exact @GlobalTheory.CompanionTheory.CompDich.dich_comp | exact GlobalTheory.CompanionTheory.CompDich.dich_comp | (intros; apply GlobalTheory.CompanionTheory.CompDich.dich_comp <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.comparable_mod_square_localization : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Val0 (S := S ⧸ Ideal.span {ϖ ^ 2}) → ∀ P : Ideal S, P.IsPrime → ∀ f g : S ⧸ compI P, f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨ g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  first | exact @GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span | exact GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span | (intros; apply GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.divided_power_quotient_exists : ∀ {S : Type} [CommRing S] , TF (S := S) → ∀ I J : Ideal S, PdI I → (∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) → ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  first | exact @GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient | exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient | (intros; apply GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.dichotomy_of_comparable_mod_square : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  first | exact @GlobalTheory.CompanionTheory.DichMod.dich_of_mod | exact GlobalTheory.CompanionTheory.DichMod.dich_of_mod | (intros; apply GlobalTheory.CompanionTheory.DichMod.dich_of_mod <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.valuation_of_local_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Idem.val_of_dich | exact GlobalTheory.CompanionTheory.Idem.val_of_dich | (intros; apply GlobalTheory.CompanionTheory.Idem.val_of_dich <;> assumption)
end
