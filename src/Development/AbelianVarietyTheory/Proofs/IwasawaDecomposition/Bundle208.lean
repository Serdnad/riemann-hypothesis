module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open IsDedekindDomain NumberField Filter Topology

namespace GlobalTheory.LevelChars.LevTriv

open Neutral.B1 Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]


open Classical in
theorem prod_localIdele_comp (z : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ)
    (F : Finset (HeightOneSpectrum (𝓞 L))) :
    ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 ∧
    ∀ w, ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).2 w =
      if w ∈ F then ((z w : (w.adicCompletion L)ˣ) : w.adicCompletion L) else 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨rfl, fun w => by simp⟩
  | insert a F ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul]
    have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
    have e2 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).2 = x.2 * y.2 := fun _ _ => rfl
    refine ⟨?_, fun w => ?_⟩
    · rw [e1, ih.1, mul_one]; rfl
    · have e : ∀ x y : FiniteAdeleRing (𝓞 L) L, (x * y) w = x w * y w := fun _ _ => rfl
      rw [e2, e, ih.2 w]
      by_cases hw : w = a
      · subst hw
        rw [localIdele_snd_self, if_neg ha, if_pos (Finset.mem_insert_self _ _), mul_one]
      · rw [(localIdele_isSupportedAt L a (z a)).2 w hw, one_mul]
        by_cases hF : w ∈ F
        · rw [if_pos hF, if_pos (Finset.mem_insert_of_mem hF)]
        · rw [if_neg hF, if_neg (fun h => (Finset.mem_insert.1 h).elim hw hF)]

theorem tendsto_prod_localIdele (z : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hz : ∀ v, IsUnitAt v (z v))
    (c : Ideles L) (hc1 : (c : AdeleRing (𝓞 L) L).1 = 1)
    (hc2 : ∀ v, (c : AdeleRing (𝓞 L) L).2 v = ((z v : (v.adicCompletion L)ˣ) : v.adicCompletion L)) :
    Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 L)) => ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (c : AdeleRing (𝓞 L) L)) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  have hA : ∀ w, ((z w : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈ A w := fun w => (hz w).le
  let g : Finset (HeightOneSpectrum (𝓞 L)) → ∀ w, A w := fun F w =>
    if w ∈ F then ⟨_, hA w⟩ else ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let o : ∀ w, A w := fun w => ⟨_, hA w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {w}] with F hF
    have hw : w ∈ F := hF (Finset.mem_singleton_self w)
    simp only [g, o, if_pos hw]
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  have h3 : Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 L)) =>
      ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).2) atTop (𝓝 (c : AdeleRing (𝓞 L) L).2) := by
    have eo : RestrictedProduct.structureMap _ A cofinite o = (c : AdeleRing (𝓞 L) L).2 := by
      apply Subtype.ext; funext w; exact (hc2 w).symm
    rw [← eo]
    refine Tendsto.congr (fun F => ?_) h2
    apply Subtype.ext; funext w
    show ((g F w : A w) : w.adicCompletion L) = _
    refine Eq.trans ?_ ((prod_localIdele_comp z F).2 w).symm
    by_cases hw : w ∈ F
    · simp only [g, if_pos hw]
    · simp only [g, if_neg hw]
  have h4 := (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h3
  have ec : (c : AdeleRing (𝓞 L) L) = ((1 : InfiniteAdeleRing L), (c : AdeleRing (𝓞 L) L).2) := Prod.ext hc1 rfl
  rw [ec]
  refine Tendsto.congr (fun F => ?_) h4
  exact Prod.ext (prod_localIdele_comp z F).1.symm rfl

theorem eq_one_fin (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : HChar L) (hU : ∀ v, v ∉ S → ψ.UnrAt v)
    (hN : ∀ v ∈ S, ψ.LevelLe v N) (f : Ideles L) (hf1 : (f : AdeleRing (𝓞 L) L).1 = 1)
    (hf : f ∈ GlobalTheory.LevelChars.levSub L S N) : ψ.1 f = 1 := by
  classical
  let u : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ := fun v =>
    ⟨(f : AdeleRing (𝓞 L) L).2 v, ((f⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v,
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) f.mul_inv,
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) f.inv_mul⟩
  have hu : ∀ v, IsUnitAt v (u v) := fun v => (hf v).1
  have hui : ∀ v, IsUnitAt v (u v)⁻¹ := fun v => by
    unfold IsUnitAt
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu v, inv_one]
  have hloc : ∀ v, ψ.1 (localIdele L v (u v)) = 1 := fun v => by
    by_cases hv : v ∈ S
    · exact hN v hv (u v) (hu v) ((hf v).2 hv)
    · exact hU v hv (u v) (hu v)
  let b : Finset (HeightOneSpectrum (𝓞 L)) → Ideles L := fun F => ∏ v ∈ F, localIdele L v (u v)
  have hb1 : ∀ F, ψ.1 (b F) = 1 := fun F => by
    simp only [b, map_prod]
    exact Finset.prod_eq_one fun v _ => hloc v
  have hfi1 : ((f⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := by
    have h := congrArg (fun y : AdeleRing (𝓞 L) L => y.1) f.inv_mul
    have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
    simp only [e1, hf1, mul_one] at h
    exact h
  have t1 := tendsto_prod_localIdele u hu f hf1 fun v => rfl
  have t2 := tendsto_prod_localIdele (fun v => (u v)⁻¹) hui f⁻¹ hfi1 fun v => rfl
  have tb : Tendsto b atTop (𝓝 f) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (Tendsto.congr (fun F => ?_) t2))
    show ((∏ v ∈ F, localIdele L v (u v)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = (((b F)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)
    congr 1
    simp only [b, map_inv, Finset.prod_inv_distrib]
  have t3 := (ψ.2.1.tendsto f).comp tb
  have t4 : Tendsto (ψ.1 ∘ b) atTop (𝓝 1) := tendsto_const_nhds.congr fun F => (hb1 F).symm
  exact tendsto_nhds_unique t3 t4

theorem infIdele_mem (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (x : (InfiniteAdeleRing L)ˣ) :
    GlobalTheory.HeckeSplit.infIdele L x ∈ GlobalTheory.LevelChars.levSub L S N := fun v => by
  have e : GlobalTheory.LevelChars.compAt L v (GlobalTheory.HeckeSplit.infIdele L x) = 1 := rfl
  refine ⟨by rw [e, map_one], fun _ => ?_⟩
  rw [e, sub_self, map_zero]
  exact zero_le

theorem infDiag_eq_infIdele (k : Lˣ) :
    infDiag k = GlobalTheory.HeckeSplit.infIdele L (Units.map (algebraMap L (InfiniteAdeleRing L)).toMonoidHom k) := by
  classical
  apply Units.ext
  show ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1)
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

theorem eq_one_inf (ψ : HChar L) (hinf : ∀ k : Lˣ, ψ.inf k = 1) (x : (InfiniteAdeleRing L)ˣ) :
    ψ.1 (GlobalTheory.HeckeSplit.infIdele L x) = 1 := by
  have hc : Continuous (GlobalTheory.HeckeSplit.infIdele L) :=
    Continuous.units_map _ (continuous_id.prodMk continuous_const)
  refine (GlobalTheory.HeckeGal.denseRange_units_inf L).induction_on x
    (isClosed_eq (ψ.2.1.comp hc) continuous_const) fun k => ?_
  rw [← infDiag_eq_infIdele]
  exact hinf k

theorem levSub_triv : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (ψ : Formalism.L2.Host.HChar L), (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) →
    ∀ a ∈ GlobalTheory.LevelChars.levSub L S N, ψ.1 a = 1 := by
  intro L _ _ S N ψ hinf hU hN a ha
  set x := GlobalTheory.HeckeSplit.infPart L a
  have hdec : a = GlobalTheory.HeckeSplit.infIdele L x * ((GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a) := by
    rw [mul_inv_cancel_left]
  have hf1 : (((GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := by
    rw [← map_inv]
    show ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 * (a : AdeleRing (𝓞 L) L).1 = 1
    have h := congrArg (fun y : AdeleRing (𝓞 L) L => y.1) a.inv_mul
    exact h
  have hmem : (GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a ∈ GlobalTheory.LevelChars.levSub L S N :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (infIdele_mem S N x)) ha
  rw [hdec, map_mul, eq_one_inf ψ hinf x, eq_one_fin S N ψ hU hN _ hf1 hmem, mul_one]

end GlobalTheory.LevelChars.LevTriv
end
end

section

open Matrix GlobalTheory.JointHarm
open scoped Classical

namespace GlobalTheory.JointHarm.OrbitMap

variable {ι : Type} {n : ℕ}

theorem one_mem_K (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by simp⟩

theorem one_mem_KC (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ GlobalTheory.Dec.KC ε :=
  ⟨isUnit_one, by simp⟩

theorem K_sub_KC {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ GlobalTheory.Dec.KC ε :=
  ⟨⟨Unitary.toUnits ⟨g, hg.1⟩, rfl⟩, hg.2⟩

theorem mul_mem_K {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε)
    (hh : h ∈ Formalism.REAL.Kset ε) : g * h ∈ Formalism.REAL.Kset ε :=
  ⟨mul_mem hg.1 hh.1, by rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]⟩

theorem star_mem_K {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    gᴴ ∈ Formalism.REAL.Kset ε := by
  have h1 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
  have h2 : g * gᴴ = 1 := Unitary.mul_star_self_of_mem hg.1
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  calc gᴴ * Formalism.REAL.Jm ε = gᴴ * (Formalism.REAL.Jm ε * g) * gᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
    _ = Formalism.REAL.Jm ε * gᴴ := by
        rw [← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem single_mem_KC {ε : ι → Fin n → Bool} {τ : ι} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.Dec.KC (ε τ)) (σ : ι) :
    (Pi.mulSingle τ g : ι → Matrix (Fin n) (Fin n) ℂ) σ ∈ GlobalTheory.Dec.KC (ε σ) := by
  by_cases h : σ = τ
  · subst h; simpa using hg
  · simpa [h] using one_mem_KC _

theorem single_comm {τ : ι} (g : Matrix (Fin n) (Fin n) ℂ) {v : ι → Matrix (Fin n) (Fin n) ℂ}
    (hv : v τ = 1) : Pi.mulSingle τ g * v = v * Pi.mulSingle τ g := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [hv]
  · simp [h]

theorem fam_induction [Fintype ι] {ε : ι → Fin n → Bool} (Q : (ι → Matrix (Fin n) (Fin n) ℂ) → Prop)
    (h1 : Q 1)
    (hs : ∀ τ k v, k ∈ Formalism.REAL.Kset (ε τ) → (∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) → v τ = 1 → Q v →
      Q (Pi.mulSingle τ k * v)) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) : Q u := by
  have key : ∀ s : Finset ι, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ,
      (∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) → (∀ σ ∉ s, u σ = 1) → Q u := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro u _ h
      have : u = 1 := funext fun σ => h σ (by simp)
      rw [this]; exact h1
    | insert τ s _ ih =>
      intro u hu h
      have hv : ∀ σ, Function.update u τ 1 σ ∈ Formalism.REAL.Kset (ε σ) := by
        intro σ
        by_cases e : σ = τ
        · subst e; simpa using one_mem_K _
        · simpa [e] using hu σ
      have e : u = Pi.mulSingle τ (u τ) * Function.update u τ 1 := by
        funext σ
        by_cases e : σ = τ
        · subst e; simp
        · simp [e]
      rw [e]
      refine hs τ _ _ (hu τ) hv (by simp) (ih _ hv fun σ hσ => ?_)
      by_cases e : σ = τ
      · subst e; simp
      · simpa [e] using h σ (by simp [e, hσ])
  exact key Finset.univ u hu (by simp)

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P} {ε : ι → Fin n → Bool} {μ : ι → Fin n → ℝ}

theorem adj_fam [Fintype ι] (h : IsHolFam ε B ϖ) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) :
    ∀ a b, B (ϖ u a) b = B a (ϖ (fun σ => (u σ)ᴴ) b) := by
  refine fam_induction (ε := ε) (fun u => ∀ a b, B (ϖ u a) b = B a (ϖ (fun σ => (u σ)ᴴ) b)) ?_ ?_ u hu
  · intro a b
    have : (fun σ => ((1 : ι → Matrix (Fin n) (Fin n) ℂ) σ)ᴴ) = 1 := by funext σ; simp
    rw [this, h.2.1]; rfl
  · intro τ k v hk hv _ ih a b
    have e : (fun σ => ((Pi.mulSingle τ k * v : ι → Matrix (Fin n) (Fin n) ℂ) σ)ᴴ) =
        (fun σ => (v σ)ᴴ) * Pi.mulSingle τ kᴴ := by
      funext σ
      by_cases e : σ = τ
      · subst e; simp
      · simp [e]
    rw [e, h.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      h.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hv σ))) (single_mem_KC (K_sub_KC (star_mem_K hk))),
      Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact (h.2.2.2 τ).2.2.2.1 k (K_sub_KC hk) _ _

theorem bottom_move (h : IsHolFam ε B ϖ) {x : P} (hx : IsBotFam ε ϖ μ x) {τ : ι}
    {v : ι → Matrix (Fin n) (Fin n) ℂ} (hv : ∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) (hτ : v τ = 1) :
    IsBottom (ε τ) (fun g => ϖ (Pi.mulSingle τ g)) (μ τ) (ϖ v x) := by
  have c : ∀ g ∈ GlobalTheory.Dec.KC (ε τ), ϖ (Pi.mulSingle τ g) (ϖ v x) = ϖ v (ϖ (Pi.mulSingle τ g) x) := by
    intro g hg
    rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      ← h.2.2.1 _ _ (single_mem_KC hg) (fun σ => K_sub_KC (hv σ)),
      ← h.2.2.1 _ _ (fun σ => K_sub_KC (hv σ)) (single_mem_KC hg), single_comm g hτ]
  refine ⟨fun g hg hl => ?_, fun θ => ?_⟩
  · show ϖ (Pi.mulSingle τ g) (ϖ v x) = _
    rw [c g hg]
    exact congrArg _ ((hx τ).1 g hg hl)
  · show ϖ (Pi.mulSingle τ _) (ϖ v x) = _
    rw [c, ← map_smul]
    · exact congrArg _ ((hx τ).2 θ)
    · refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.exp_ne_zero _

variable {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ}
  {ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P'}

theorem coef_fam [Fintype ι] (h : IsHolFam ε B ϖ) (h' : IsHolFam ε B' ϖ') {x : P} {x' : P'}
    (hx : IsBotFam ε ϖ μ x) (hx' : IsBotFam ε ϖ' μ x') (h0 : x' ≠ 0)
    (u : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) :
    B x (ϖ u x) * B' x' x' = B x x * B' x' (ϖ' u x') := by
  have hc : B' x' x' ≠ 0 := fun e => h0 (h'.1 _ e)
  refine fam_induction (ε := ε) (fun u => B x (ϖ u x) * B' x' x' = B x x * B' x' (ϖ' u x')) ?_ ?_ u hu
  · show B x (ϖ 1 x) * B' x' x' = B x x * B' x' (ϖ' 1 x')
    rw [h.2.1, h'.2.1]; rfl
  · intro τ k v hk hv hτ ih
    have e1 := GlobalTheory.JointHarm.Sph.coeff_eq n (ε τ) (μ τ) P B _ P' B' _ x (ϖ v x) x' x' (h.2.2.2 τ) (h'.2.2.2 τ)
      (hx τ) (bottom_move h hx hv hτ) (hx' τ) (hx' τ) k hk
    have e2 := GlobalTheory.JointHarm.Sph.coeff_eq n (ε τ) (μ τ) P' B' _ P' B' _ x' (ϖ' v x') x' x' (h'.2.2.2 τ) (h'.2.2.2 τ)
      (hx' τ) (bottom_move h' hx' hv hτ) (hx' τ) (hx' τ) k hk
    show B x (ϖ (Pi.mulSingle τ k * v) x) * B' x' x' = B x x * B' x' (ϖ' (Pi.mulSingle τ k * v) x')
    rw [h.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      h'.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      Module.End.mul_apply, Module.End.mul_apply]
    apply mul_right_cancel₀ hc
    linear_combination (B' x' x') * e1 - (B x x) * e2 + (B' x' (ϖ' (Pi.mulSingle τ k) x')) * ih

theorem gram_fam [Fintype ι] (h : IsHolFam ε B ϖ) (h' : IsHolFam ε B' ϖ') {x : P} {x' : P'}
    (hx : IsBotFam ε ϖ μ x) (hx' : IsBotFam ε ϖ' μ x') (h0 : x' ≠ 0)
    (u v : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ))
    (hv : ∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) :
    B (ϖ u x) (ϖ v x) * B' x' x' = B x x * B' (ϖ' u x') (ϖ' v x') := by
  rw [adj_fam h u hu, adj_fam h' u hu, ← Module.End.mul_apply, ← Module.End.mul_apply,
    ← h.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hu σ))) (fun σ => K_sub_KC (hv σ)),
    ← h'.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hu σ))) (fun σ => K_sub_KC (hv σ))]
  exact coef_fam h h' hx hx' h0 _ fun σ => mul_mem_K (star_mem_K (hu σ)) (hv σ)

theorem exists_map_of_gram {U : Type} (f : U → P) (f' : U → P') (hB : ∀ y, B y y = 0 → y = 0)
    {c d : ℂ} (hc : c ≠ 0) (hg : ∀ u v, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u, ψ (f' u) = f u := by
  first
  | exact @_root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram
  | exact _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram
  | (apply _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> assumption)
  | (intros; apply _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram ..)

theorem exists_orbit_map : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (μ : ι → Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P') (x : P) (x' : P'), IsHolFam ε B ϖ → IsHolFam ε B' ϖ' → IsBotFam ε ϖ μ x → IsBotFam ε ϖ' μ x' → x' ≠ 0 → ∃ ψ : P' →ₗ[ℂ] P, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)) → ψ (ϖ' u x') = ϖ u x := by
  intro ι _ n ε μ P _ _ B ϖ P' _ _ B' ϖ' x x' h h' hx hx' h0
  obtain ⟨ψ, hψ⟩ := exists_map_of_gram (B := B) (B' := B')
    (U := {u : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)})
    (fun u => ϖ u.1 x) (fun u => ϖ' u.1 x') h.1 (fun e => h0 (h'.1 _ e))
    (fun u v => gram_fam h h' hx hx' h0 u.1 v.1 u.2 v.2)
  exact ⟨ψ, fun u hu => hψ ⟨u, hu⟩⟩

end GlobalTheory.JointHarm.OrbitMap
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialAction_one_mul_adjoint : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), fact (n := n) ε x₁ x₂ x₃ 1 1 = 1 ∧ (∀ (k k' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u u' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, k' τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → (∀ τ, IsUnit (u' τ)) → fact ε x₁ x₂ x₃ (k * k') (u * u') = fact ε x₁ x₂ x₃ k u * fact ε x₁ x₂ x₃ k' u') ∧ ∀ (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → ∀ F F' : PolF D m n, fockL (fact ε x₁ x₂ x₃ k u F) F' = fockL F (fact ε x₁ x₂ x₃ (fun τ => (k τ)ᴴ) (fun τ => (u τ)ᴴ) F') := by
  first | exact @GlobalTheory.JointHarm.fact_one_mul_adj | exact GlobalTheory.JointHarm.fact_one_mul_adj | (intros; apply GlobalTheory.JointHarm.fact_one_mul_adj <;> assumption)
end

section

noncomputable section

open GlobalTheory.DefLift

namespace GlobalTheory.RowSupport

theorem exp_I_pow_injective : Function.Injective fun e : ℕ => Complex.exp Complex.I ^ e := by
  intro a b h
  simp only [← Complex.exp_nat_mul] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h2 : (a : ℝ) = b + k * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simpa using this
  by_cases h0 : k = 0
  · subst h0
    exact_mod_cast (by simpa using h2 : (a : ℝ) = b)
  · exfalso
    have h3 : (2 * k : ℤ) ≠ 0 := mul_ne_zero two_ne_zero h0
    refine (irrational_pi.intCast_mul h3).ne_int ((a : ℤ) - b) ?_
    push_cast
    linarith

def scal (m : ℕ) : Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨Complex.exp Complex.I • 1, by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, mul_one]
    have : Complex.exp Complex.I * star (Complex.exp Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    rw [this, one_smul]⟩

open Classical in
theorem rowSub_scal {ι : Type} [Fintype ι] {m n : ℕ} (τ : ι) (α : ι × Fin m × Fin n →₀ ℕ) :
    rowSub n τ (scal m) (MvPolynomial.monomial α 1) =
      Complex.exp Complex.I ^ (∑ v, if v.1 = τ then α v else 0) • MvPolynomial.monomial α 1 := by
  have hv : ∀ v : ι × Fin m × Fin n,
      (∑ i, ∑ c, ((if v.1 = τ then (scal m : Matrix (Fin m) (Fin m) ℂ) else 1) i v.2.1 *
        (1 : Matrix (Fin n) (Fin n) ℂ) v.2.2 c) • (MvPolynomial.X (v.1, i, c) : Pol ι m n)) =
      (if v.1 = τ then Complex.exp Complex.I else 1) • MvPolynomial.X v := by
    rintro ⟨ρ, j, d⟩
    by_cases h : ρ = τ
    · simp [h, scal, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [h, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  unfold rowSub subst
  rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, map_one, one_mul, MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [hv, smul_pow]
  rw [Finset.prod_smul, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem exists_degree_bound (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X) (β : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ)
    (h : ∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) :
    ∃ d : ℕ, ∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → β (MvPolynomial.monomial α 1) = 0 := by
  classical
  have hfin : ∀ τ, ∃ d : ℕ, ∀ e : ℕ,
      Module.End.HasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
        (Complex.exp Complex.I ^ e)⁻¹ → e ≤ d := by
    intro τ
    have h1 := Module.End.finite_hasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
    have h2 := h1.preimage (f := fun e : ℕ => (Complex.exp Complex.I ^ e)⁻¹)
      (inv_injective.comp exp_I_pow_injective).injOn
    obtain ⟨d, hd⟩ := h2.bddAbove
    exact ⟨d, fun e he => hd he⟩
  choose d hd using hfin
  refine ⟨∑ τ, d τ, fun α hα => ?_⟩
  by_contra hne
  have hdeg : α.degree = ∑ τ, ∑ v, if v.1 = τ then α v else 0 := by
    rw [Finset.sum_comm, Finsupp.degree_eq_sum]
    simp
  refine absurd hα (not_lt.2 ?_)
  rw [hdeg]
  refine Finset.sum_le_sum fun τ _ => hd τ _ ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := β (MvPolynomial.monomial α 1)) ⟨?_, hne⟩
  rw [Module.End.mem_eigenspace_iff]
  ext x
  have := h τ (scal m) (MvPolynomial.monomial α 1) x
  rw [rowSub_scal, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  rw [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ (Complex.exp_ne_zero _))]
  convert this

end GlobalTheory.RowSupport

end
end
