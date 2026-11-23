module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Y0_mul_apply {a n : ℕ} (M : Matrix (Fin (a + n)) (Fin (a + n)) k) (i : Fin n) (j : Fin (a + n)) :
    (Y0 k n (a + n) * M) i j = M (Fin.natAdd a i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd a i)]
  · simp [Y0]
  · intro l _ hl
    have : ¬ ((l : ℕ) = a + i) := fun h => hl (Fin.ext (by simp; omega))
    simp [Y0, this]
  · simp

theorem mul_Y0_apply {a n : ℕ} (D : Matrix (Fin n) (Fin n) k) (i : Fin n) (j : Fin (a + n)) :
    (D * Y0 k n (a + n)) i j = if h : a ≤ (j : ℕ) then D i ⟨j - a, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j - a, by omega⟩ : Fin n)]
    · simp [Y0]; omega
    · intro l _ hl
      have : ¬ ((j : ℕ) = a + l) := fun h' => hl (Fin.ext (by simp; omega))
      simp [Y0, this]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ¬ ((j : ℕ) = a + l) := by omega
    simp [Y0, this]

theorem Y0_mul_parab {a n : ℕ} (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    Y0 k n (a + n) * (p : GL (Fin (a + n)) k).1 =
      (leviProj k (GlobalTheory.RankFibre.blocks a n) p true : GL (Fin n) k).1 * Y0 k n (a + n) := by
  ext i j
  rw [Y0_mul_apply, mul_Y0_apply]
  have hp := (mem_parab_two k).1 p.2
  split_ifs with h
  · rw [leviProj_apply]
    have e1 : GlobalTheory.RankFibre.blocks a n ⟨true, i⟩ = Fin.natAdd a i := Fin.ext (by simp [stdSum])
    have e2 : GlobalTheory.RankFibre.blocks a n ⟨true, (⟨j - a, by omega⟩ : Fin n)⟩ = j := Fin.ext (by simp [stdSum]; omega)
    rw [e1, e2]
  · have := hp i ⟨j, by omega⟩
    simpa [stdSum] using this

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parChar_eq {a n : ℕ} (ν : kˣ →* ℂˣ) (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    ((GlobalTheory.RankFibre.parChar ν ν⁻¹ a n p : ℂˣ) : ℂ) =
      apow (gdet (p : GL (Fin (a + n)) k)) ((n : ℂ) / 2) *
        ((((ν (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)))⁻¹ : ℂˣ) : ℂ) *
          apow (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)) (-((a + n : ℕ) : ℂ) / 2)) := by
  set A := leviProj k (GlobalTheory.RankFibre.blocks a n) p false
  set D := leviProj k (GlobalTheory.RankFibre.blocks a n) p true
  have hδ : deltaHalf k (Two (Fin a) (Fin n)) (leviProj k (GlobalTheory.RankFibre.blocks a n) p) =
      absPow k ((n : ℂ) / 2) (gdet A) * absPow k (-(a : ℂ) / 2) (gdet D) := by
    rw [← (leviTwo k (Fin a) (Fin n)).apply_symm_apply (leviProj k (GlobalTheory.RankFibre.blocks a n) p), deltaHalf_two]
    simp [A, D]
    rfl
  have hdet : gdet (p : GL (Fin (a + n)) k) = gdet A * gdet D := by
    rw [gdet, det_parab, Fintype.prod_bool, mul_comm]
  simp only [GlobalTheory.RankFibre.parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hδ]
  rw [hdet, apow_mul]
  have e : apow (gdet D) (-(a : ℂ) / 2) =
      apow (gdet D) ((n : ℂ) / 2) * apow (gdet D) (-((a + n : ℕ) : ℂ) / 2) := by
    rw [← apow_add]; congr 1; push_cast; ring
  show apow (gdet A) ((n : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * (((ν * ν⁻¹) (gdet A) : ℂˣ) : ℂ) *
    ((ν⁻¹ (gdet D) : ℂˣ) : ℂ) = _
  rw [e, mul_inv_cancel]
  simp only [MonoidHom.one_apply, Units.val_one, mul_one, MonoidHom.inv_apply]
  ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detTw (d : ℕ) (s : ℂ) : (GL (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ) where
  toFun f x := apow (gdet x) s * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp; ring

theorem detTw_apply (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (x : GL (Fin d) k) :
    detTw d s f x = apow (gdet x) s * f x := rfl

theorem detTw_neg_detTw (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d (-s) (detTw d s f) = f := by
  funext x; rw [detTw_apply, detTw_apply, ← mul_assoc, ← apow_add]; simp

theorem detTw_detTw_neg (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d s (detTw d (-s) f) = f := by
  simpa using detTw_neg_detTw d (-s) f

theorem detTw_translate (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (h : GL (Fin d) k) :
    (fun x => detTw d s f (x * h)) = apow (gdet h) s • detTw d s (fun x => f (x * h)) := by
  funext x
  simp only [detTw_apply, Pi.smul_apply, smul_eq_mul, gdet_mul, apow_mul]
  ring

theorem detTw_mem_indScal {a n : ℕ} (ν : kˣ →* ℂˣ) {f : GL (Fin (a + n)) k → ℂ} (hf : f ∈ indSp k n (a + n) ν) :
    detTw (a + n) ((n : ℂ) / 2) f ∈ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := by
  obtain ⟨⟨U, hU, hfU⟩, hfl⟩ := hf
  have hK : IsSmoothChar (detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))) :=
    (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have hK1 : ((detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))).ker : Set (GL (Fin (a + n)) k)) ∈ nhds 1 :=
    hK.mem_nhds (by simp)
  refine ⟨mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem hU hK1) fun g hg => ?_), ?_⟩
  · have hg2 : apow (gdet g) ((n : ℂ) / 2) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hg.2)
      exact this
    show (fun x => detTw (a + n) ((n : ℂ) / 2) f (x * g)) = detTw (a + n) ((n : ℂ) / 2) f
    funext x
    simp only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hfU x g hg.1]
  · intro p x
    have h := hfl p x (leviProj k (GlobalTheory.RankFibre.blocks a n) p true) (Y0_mul_parab p)
    simp only [ofChar_apply, detTw_apply, gdet_mul, apow_mul, h, parChar_eq]
    ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv

open IndTwist

theorem indSp_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  intro P k _ _ _ _ n d ν hn hνs hνu N hN hinv
  obtain ⟨a, rfl⟩ : ∃ a, d = a + n := ⟨d - n, by omega⟩
  have hu : IsUnitaryChar ν⁻¹ := fun g => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hνu g, inv_one]
  set s : ℂ := (n : ℂ) / 2
  let M : Submodule ℂ (GL (Fin (a + n)) k → ℂ) := N.comap (detTw (a + n) (-s))
  have hMle : M ≤ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := fun g hg => by
    have := detTw_mem_indScal ν (hN hg)
    rwa [detTw_detTw_neg] at this
  have hMinv : ∀ g ∈ M, ∀ h : GL (Fin (a + n)) k, (fun x => g (x * h)) ∈ M := fun g hg h => by
    show detTw (a + n) (-s) (fun x => g (x * h)) ∈ N
    have e : detTw (a + n) (-s) (fun x => g (x * h)) =
        apow (gdet h) s • (fun x => detTw (a + n) (-s) g (x * h)) := by
      rw [detTw_translate, smul_smul, ← apow_add]; simp
    rw [e]
    exact N.smul_mem _ (hinv _ hg h)
  have hmemM : ∀ f ∈ N, detTw (a + n) s f ∈ M := fun f hf => by
    show detTw (a + n) (-s) (detTw (a + n) s f) ∈ N
    rwa [detTw_neg_detTw]
  rcases GlobalTheory.RankFibre.indScal_irreducible P.bernsteinUnitaryProductIrreducible k a n ν ν⁻¹ hνs hνu hνs.inv hu
    M hMle hMinv with h | h
  · left
    refine (Submodule.eq_bot_iff N).2 fun f hf => ?_
    have h0 : detTw (a + n) s f = 0 := by
      have := hmemM f hf
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    rw [← detTw_neg_detTw (a + n) s f, h0, map_zero]
  · right
    refine le_antisymm hN fun f hf => ?_
    have := h (detTw_mem_indScal ν hf)
    have h' : detTw (a + n) (-s) (detTw (a + n) s f) ∈ N := this
    rwa [detTw_neg_detTw] at h'

end GlobalTheory.FullRankCoinv
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixEvAdm

theorem coset_indicator_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (N v : Set (v.adicCompletion F))) → (∀ v, IsCompact (N v : Set (v.adicCompletion F))) →
    (∀ᶠ v in Filter.cofinite, (N v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ a : κ → FiniteAdeleRing (𝓞 F) F, ∃ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
        Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - a i) ∈ N v} 1 y =
          ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
  intro F _ _ κ _ N hNo hNc hNcof a
  classical
  have hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∀ c : κ → v.adicCompletion F,
      IsOpen {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} ∧
      IsClosed {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} ∧
      IsCompact {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} := by
    intro v c
    have e : {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} =
        (fun x => x - c) ⁻¹' Set.pi Set.univ fun _ => (N v : Set (v.adicCompletion F)) := by
      ext x; simp
    have hcl : IsClosed (N v : Set (v.adicCompletion F)) := (N v).isClosed_of_isOpen (hNo v)
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hNo v).preimage (continuous_sub_right c)
    · rw [e]; exact (isClosed_set_pi fun _ _ => hcl).preimage (continuous_sub_right c)
    · have e2 : {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} =
          (Homeomorph.subRight c).symm '' Set.pi Set.univ fun _ => (N v : Set (v.adicCompletion F)) := by
        rw [e, Homeomorph.image_symm]; rfl
      rw [e2]
      exact (isCompact_univ_pi fun _ => hNc v).image (Homeomorph.subRight c).symm.continuous
  have hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite,
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F := fun y =>
    Filter.eventually_all.2 fun i => (y i).2
  refine ⟨fun v => Set.indicator {x | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i) ∈ N v} 1, fun v => ?_, ?_, fun y => ?_⟩
  · obtain ⟨ho, hc, hk⟩ := hS v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i)
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
      HasCompactSupport.intro hk fun y hy => Set.indicator_of_notMem hy _⟩
    set Sx := {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i) ∈ N v} with hSx
    by_cases hx : x ∈ Sx
    · filter_upwards [ho.mem_nhds hx] with z hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show z ∈ Sx from hz)]
      rfl
    · filter_upwards [hc.isOpen_compl.mem_nhds hx] with z hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show z ∉ Sx from hz)]
  · filter_upwards [hNcof, hint a] with v hv ha
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [← SetLike.mem_coe, hv, SetLike.mem_coe]
    exact ⟨fun h => by simpa using add_mem h (ha i), fun h => sub_mem h (ha i)⟩
  · by_cases hy : y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - a i) ∈ N v}
    · rw [Set.indicator_of_mem hy, Pi.one_apply]
      refine (finprod_eq_one_of_forall_eq_one fun v => ?_).symm
      refine Set.indicator_of_mem (fun i => ?_) _
      simpa [map_sub] using hy i v
    · rw [Set.indicator_of_notMem hy]
      simp only [Set.mem_setOf_eq, not_forall] at hy
      obtain ⟨i, v, hv⟩ := hy
      refine (finprod_eq_zero _ v (Set.indicator_of_notMem (show (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y j)) ∉ {x | ∀ j, x j - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a j) ∈ N v} from fun h => hv (by simpa [map_sub] using h i)) _) ?_).symm
      refine (Filter.eventually_cofinite.1 ((hNcof.and (hint a)).and (hint y))).subset fun w hw h' => hw ?_
      refine Set.indicator_of_mem (fun j => ?_) _
      rw [← SetLike.mem_coe, h'.1.1, SetLike.mem_coe]
      exact sub_mem (h'.2 j) (h'.1.2 j)

end GlobalTheory.MixEvAdm

namespace GlobalTheory.MixEvAdm

theorem sb_decomp : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
      (∀ j v, φ j v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      (∀ j, ∀ᶠ v in Filter.cofinite, φ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
  intro F _ _ κ _ g hg
  classical
  have h1 : ∀ᶠ t in 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F), ∀ z ∈ tsupport g, g (z + t) = g z := by
    refine IsCompact.eventually_forall_of_forall_eventually hg.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        (g (q.2 + q.1), g q.2) :=
      (hg.1.comp_continuous (by fun_prop)).prodMk (hg.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨N, hNo, hNc, hNcof, hPn, hPV⟩ := GlobalTheory.T.exists_compact_open_subgroups F κ _ h1
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    { carrier := {y | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v}
      zero_mem' := fun i v => by simp
      add_mem' := fun ha hb i v => by simpa [map_add (f := _)] using add_mem (ha i v) (hb i v)
      neg_mem' := fun ha i v => by simpa [map_neg] using neg_mem (ha i v) }
  have hinv : ∀ u ∈ U, ∀ z, g (z + u) = g z := fun u hu z => by
    by_cases hz : z ∈ tsupport g
    · exact hPV hu z hz
    by_cases hz' : z + u ∈ tsupport g
    · have := hPV (U.neg_mem hu) _ hz'
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']
  obtain ⟨t, -, ht⟩ := hg.2.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set _))
    (fun a _ => (continuous_sub_right a).continuousAt.preimage_mem_nhds (by show (U : Set _) ∈ 𝓝 (a - a); rw [sub_self]; exact hPn))
  set Tq := t.image (QuotientAddGroup.mk : _ → _ ⧸ U)
  have hind : ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) (q : _ ⧸ U),
      Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} 1 y =
        if (y : _ ⧸ U) = q then (1 : ℂ) else 0 := by
    intro y q
    have : (y : _ ⧸ U) = q ↔ y - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    by_cases h : y - q.out ∈ U
    · rw [Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v,
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} from h), if_pos (this.mpr h), Pi.one_apply]
    · rw [Set.indicator_of_notMem (show y ∉ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v,
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} from h), if_neg (fun h' => h (this.mp h'))]
  have key : ∀ y, g y = ∑ q ∈ Tq, g q.out *
      Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} 1 y := by
    intro y
    simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
    split_ifs with h
    · have h2 : -y + (y : _ ⧸ U).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
      have := hinv _ h2 y
      rw [add_neg_cancel_left] at this
      exact this.symm
    · by_contra hne
      have hy : y ∈ tsupport g := subset_tsupport _ hne
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
      refine h (Finset.mem_image.mpr ⟨x, hx, ?_⟩)
      exact (QuotientAddGroup.eq_iff_sub_mem.mpr hyx).symm
  choose φq hφSB hφstd hφeq using fun q : _ ⧸ U => coset_indicator_finprod F κ N hNo hNc hNcof q.out
  let e := Tq.equivFin
  refine ⟨Tq.card, fun j => g (e.symm j).1.out, fun j => φq (e.symm j).1, fun j v => hφSB _ v, fun j => hφstd _, ?_⟩
  funext y
  rw [key y]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hφeq]
  rw [← Finset.sum_coe_sort Tq]
  exact (Equiv.sum_comp e.symm (fun q : Tq => g q.1.out * ∏ᶠ v, φq q.1 v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))).symm

end GlobalTheory.MixEvAdm

namespace GlobalTheory.MixEvAdm

theorem pullback_adm : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ _ hP₁ e hE l hl
  intro g hg
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hfam : ∀ j, ∀ᶠ v in Filter.cofinite, φ j v = M.vac v := fun j =>
    ((hstd j).and hP.good.std).mono fun v hv => hv.1.trans hv.2.symm
  have hψSB : ∀ j v, ev v (φ j v) ∈ SB (Fin n₁ × Fin d → Fv F v) := fun j v =>
    (hev v).2 ▸ Submodule.mem_map_of_mem (hφ j v)
  have hψstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      ev v (φ j v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hfam j).and hP₁.good.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]
  have hG : ∀ j, (fun y : Fin n₁ × Fin d → Af F => ∏ᶠ v, ev v (φ j v) fun i => evalV F v (y i)) ∈
      SB (Fin n₁ × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  choose Tj hTj using fun j => hl _ (hG j)
  refine ⟨∑ j, c j • (Tj j).comp ei, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl

  rw [LinearMap.comp_apply, hsplit, map_sum, map_sum]
  simp only [map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hloc f (φ j) (hφ j) (hfam j)]
  exact congrArg (c j • ·) (hTj j (ei f))

end GlobalTheory.MixEvAdm
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchSurj

theorem exists_point_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (hne : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y : κ → Af F, ∀ v, φ v (fun i => y i v) ≠ 0 := by
  have key : ∀ v : Pl (F := F), ∃ z : κ → Fv F v, φ v z ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, z i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨z, hz⟩ := Function.ne_iff.mp (hne v)
    refine ⟨z, hz, fun h => ?_⟩
    rw [h] at hz
    exact Set.mem_of_indicator_ne_zero hz
  choose z hz hz' using key
  exact ⟨fun i => ⟨fun v => z v i, hstd.mono fun v hv => hz' v hv i⟩, hz⟩

theorem surjective_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.SurjOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Surjective ei := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM hM₁ e hsurj ei ev hev he h
  have h₁ : pure h M₁.vac ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA h M₁.vac (fun v => (hM₁.vac v).1) hM₁.std
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj h₁
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = M.vac v := by
    intro i
    filter_upwards [hM.std, T.eventually_cofinite_notMem] with v hv hT
    rw [hv, hstd i v hT]
  have hid : pure h M₁.vac = ∑ i, pure (ei (f i)) fun v => ev v (φ i v) := by

    rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨y, hy⟩ := exists_point_ne_zero M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  set c : ℂ := ∏ᶠ v, M₁.vac v (fun j => y j v) with hc
  have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
  set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
  refine ⟨∑ i, (cs i / c) • f i, ?_⟩
  refine DFunLike.ext _ _ fun x => ?_
  let a : Fin n × Fin d → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
  have hI : (fun j => evI F (a j)) = x := by
    funext j
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
  have hx : h x * c = ∑ i, ei (f i) x * cs i := by
    have := congrFun hid a
    rw [Finset.sum_apply] at this
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
    exact this

  rw [map_sum]
  have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
    rw [SchwartzMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]; rfl
  rw [hs]
  apply mul_right_cancel₀ hc0
  rw [hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end GlobalTheory.ArchSurj
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

theorem _root_.GlobalTheory.T.squareBottomPairs_small_reference_tuple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m) 𝔪, IsBottom G μ₀ i j 𝔪 P P' → P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap) := by
  first | exact @GlobalTheory.BotSmall.bottom_small | exact GlobalTheory.BotSmall.bottom_small | (intros; apply GlobalTheory.BotSmall.bottom_small <;> assumption)
end
