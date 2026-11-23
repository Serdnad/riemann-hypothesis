module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle015
public import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.IndicatorMem
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
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
import Mathlib.RingTheory.Finiteness.Lattice
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
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle049
public import Development.WeilBound.ThetaLifts.LatticeBasics.SliceSeminorm

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem polFin {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χX χW} {om : Rep σ Y W} {r s r' s'}
    (h : IsPair B M χX χW om r s r' s') : ∀ f ∈ M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)),
      FiniteDimensional ℂ U ∧ ∀ k ∈ KInf σ W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U := by
  intro f hf
  have hψ := h.base.std
  have hs := h.weil.isUSplitting.toIsSplitting
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
        ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U}
      zero_mem' := ⟨⊥, inferInstance, fun k _ A _ => by rw [map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1⟩ ⟨N', _, h2⟩
        exact ⟨N ⊔ N', inferInstance, fun k hk A hA => by
          rw [map_add (f := _)]; exact Submodule.add_mem_sup (h1 k hk A hA) (h2 k hk A hA)⟩
      smul_mem' := fun c f ⟨N, h0, h1⟩ => ⟨N, h0, fun k hk A hA => by rw [map_smul]; exact N.smul_mem c (h1 k hk A hA)⟩ }
  have hfS : f ∈ S := by
    refine (sInf_le (a := S) ⟨fun f₀ h₀ => ?_, fun u hu g ⟨N, h0, h1⟩ g₁ hg => ?_⟩ : M.Pol B.ψ B.emb ≤ S) hf
    · haveI := Dense.vacSp_fin h.base.cm M B.emb
      refine ⟨⨆ ε, Dense.vacSp M B.emb ε, inferInstance, fun k hk A hA => ?_⟩
      have hgauss : M.IsGauss B.ψ B.emb (A f₀) := by
        obtain ⟨ε, hε⟩ := h₀
        refine ⟨ε, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
        set N := (mat k⁻¹).transpose with hN
        have hNk : N * (mat k).transpose = 1 := by
          rw [hN, ← Matrix.transpose_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.transpose_one]
        have e1 : u * N * (mat k).transpose = u := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have e2 : u' * N * (mat k).transpose = u' := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have hf1 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hf
        have hf2 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu' hf'
        have i1 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀
        have i2 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀
        rw [e1, ← hf1] at i1
        rw [e2, ← hf2] at i2
        have hcomm : ∀ w, Commute ((mat k⁻¹).map (piInf (B.emb w))) (W.θ w) := fun w => by
          have hc : Commute ((mat k).map (piInf (B.emb w))) (W.θ w) := hk.2 w
          have h1 : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
          have h2 : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
          show _ * _ = _ * _
          calc (mat k⁻¹).map (piInf (B.emb w)) * W.θ w
              = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w * ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by
                rw [h2, Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) * (mat k⁻¹).map (piInf (B.emb w)) := by
                simp only [Matrix.mul_assoc]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * ((mat k).map (piInf (B.emb w)) * W.θ w) * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [hc.eq]
            _ = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hrel' : ∀ w, (u' * N).map (piInf (B.emb w)) =
            (((ε w : ℤ) : ℂ) * Complex.I) • (Y.θ w * (u * N).map (piInf (B.emb w)) * (W.θ w).transpose) := fun w => by
          have hN' : N.map (piInf (B.emb w)) = ((mat k⁻¹).map (piInf (B.emb w))).transpose := by
            rw [hN, Matrix.transpose_map]
          have hc : (W.θ w).transpose * N.map (piInf (B.emb w)) = N.map (piInf (B.emb w)) * (W.θ w).transpose := by
            rw [hN', ← Matrix.transpose_mul, ← Matrix.transpose_mul, (hcomm w).eq]
          rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.smul_mul]
          simp only [Matrix.mul_assoc, hc]
        have hg := hε (u * N) (u' * N) (PositivityTheory.ThKOwn.KPol.at_mul hu N) (PositivityTheory.ThKOwn.KPol.at_mul hu' N) hrel' _ _
          (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀) (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀)
        rw [← i1, ← i2, hg, map_smul]
      obtain ⟨ε, hε⟩ := hgauss
      exact Submodule.mem_iSup_of_mem ε fun u u' hu hu' e => hε u u' hu hu' e _ _ (Dense.actsD_dop M hψ hu _)
        (Dense.actsD_dop M hψ hu' _)
    · obtain ⟨N', h3, h4⟩ := Dense.exists_dop_fin N
      refine ⟨N', h3, fun k hk A hA => ?_⟩
      rw [PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hg, PositivityTheory.ThKOwn.KPol.inter hψ hs hA hu]
      exact h4 _ _ _ (h1 k hk A hA)
  change ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
    ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U at hfS
  obtain ⟨U, h0, h1⟩ := hfS
  refine ⟨U, h0, fun k hk f₁ h₁ => ?_⟩
  obtain ⟨A, hA⟩ := PositivityTheory.ThKOwn.KPol.exists_impl fun f => PositivityTheory.ThKOwn.KPol.exists_arch_operator hψ hs hk.1 f
  rw [PositivityTheory.ThKOwn.KPol.acts_unique hA h₁]
  exact h1 k hk A hA

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open GlobalTheory.SplitFlip PositivityTheory.KCo
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}

def SplitModel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v),
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∃ ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ),
        Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) ∧
        (∀ g ∈ UAt σ X (evFin F v), ∃ g₀, Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)

theorem exists_inv' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {ι : (X → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB X : Set _) (SB Y : Set _)) : ∃ j : (Y → ℂ) →ₗ[ℂ] (X → ℂ),
      (∀ Φ ∈ SB Y, j Φ ∈ SB X ∧ ι (j Φ) = Φ) ∧ ∀ φ ∈ SB X, j (ι φ) = φ := by
  obtain ⟨q, hq⟩ := (ι ∘ₗ (SB X).subtype).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun a b h =>
    Subtype.ext (hb.2.1 a.2 b.2 h))
  have k : ∀ φ ∈ SB X, (q (ι φ)).1 = φ := fun φ h => congrArg Subtype.val (LinearMap.congr_fun hq ⟨φ, h⟩)
  refine ⟨(SB X).subtype ∘ₗ q, fun Φ h => ⟨(q Φ).2, ?_⟩, k⟩
  obtain ⟨φ, h1, rfl⟩ := hb.2.2 h
  exact congrArg ι (k φ h1)

theorem intersection_update_fsHerm_neg_one {κ : Type} [Fintype κ] (v : Pl F) (f : SInf F κ) {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1) :
    ∃ T : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), (∀ ψ, T ψ = pure f (Function.update φ v ψ)) ∧
      (∀ ψ ∈ SB _, T ψ ∈ schA F κ) ∧ ∀ S, ∀ ψ ∈ SB _, ∀ ψ₁, Acts (evFin F v) S ψ ψ₁ → S (T ψ) = T ψ₁ := by
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h2
  have m : ∀ ψ ∈ SB _, tens (evFin F v) ψ r ∈ schA F κ := fun ψ hψ => by
    rw [hr']
    refine PositivityTheory.KCo.pure_mem_schA f _ (fun u => ?_) (GlobalTheory.PureFactor.update_eventually φ v ψ h2)
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self]
    · rw [Function.update_of_ne hu]; exact h1 u
  exact ⟨{ toFun := fun ψ => tens (evFin F v) ψ r, map_add' := fun _ _ => funext fun _ => add_mul _ _ _
           map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }, hr', m, fun S ψ hψ ψ₁ h => h r ⟨hr, m ψ hψ⟩⟩

theorem acts_of_reads {v : Pl F} {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {S R}
    (h : Reads v ι S R) {j : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)}
    (h2 : ∀ φ ∈ SB _, j (ι φ) = φ) {φ} (hφ : φ ∈ SB _) : j (R (ι φ)) ∈ SB _ ∧ Acts (evFin F v) S φ (j (R (ι φ))) := by
  obtain ⟨φ₁, a, b, c⟩ := h φ hφ
  rw [← c, h2 φ₁ a]
  exact ⟨a, b⟩

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_real (x : kˣ) (m : ℕ) : ∃ r : ℝ, 0 < r ∧ apow x ((m : ℂ) / 2) = r :=
  ⟨GlobalTheory.SplitWeil.nabs k x ^ ((m : ℝ) / 2), Real.rpow_pos_of_pos (GlobalTheory.SplitWeil.nabs_pos k x) _, by
    rw [Complex.ofReal_cpow (GlobalTheory.SplitWeil.nabs_pos k x).le]; simp [apow]⟩

theorem omB_right (ν α : kˣ →* ℂˣ) (h : GL (Fin d) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α 1 h Φ = ((α (gdet h) : ℂ) * apow (gdet h) ((n : ℂ) / 2)) • fun Y => Φ (Y * h.1) := funext fun Y => by
  simp [omB, gdet]

theorem omB_left (ν α : kˣ →* ℂˣ) (g : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α g 1 Φ = ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) • fun Y => Φ (g.1ᵀ * Y) := funext fun Y => by
  simp [omB, gdet]

theorem sb_star {A : Type} [TopologicalSpace A] {f : A → ℂ} (h : f ∈ SB A) : star f ∈ SB A :=
  ⟨h.1.comp star, h.2.comp_left (g := star) (star_zero _)⟩

end Loc

variable {B : Base F E} {X : Spc F E n} {X' : Spc F E n'} {W : Spc F E d} {M' : Model σ X' W}

theorem inv_loc (hL : LocDist) (e : Fin n ⊕ Fin n' ≃ Fin d) (hM' : M'.IsGood B.ψ) {v : Pl F} {om : Rep σ X W} {om' : Rep σ X' W}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
    {ι' : ((Fin n' × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n') (Fin d) (Fv F v) → ℂ)}
    (b : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (b' : Set.BijOn ι' (SB (Fin n' × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n') (Fin d) (Fv F v)) : Set _))
    {ν ν' α α' : (Fv F v)ˣ →* ℂˣ} (n1 : ∀ x, ‖(ν x : ℂ)‖ = 1) (n2 : ∀ x, ‖(α x : ℂ)‖ = 1) (hν : ∀ x, ν x = α x / α' x)
    (hne : ν (unifAt v) ≠ 1) (L : Fn F n' d →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ)
    (hh : ∀ h₀, ∃ h, Reads v ι (om (1, h)) (omB ν α 1 h₀) ∧ Reads v ι' (om' (1, h)) (omB ν' α' 1 h₀) ∧
      ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, L (om' (1, h) Φ) (om (1, h) Ψ) = L Φ Ψ)
    {u g₀} (hu : Reads v ι (om (u, 1)) (omB ν α g₀ 1)) : ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, L Φ (om (u, 1) Ψ) = L Φ Ψ := by
  obtain ⟨j, j1, j2⟩ := exists_inv' b
  obtain ⟨j', j1', j2'⟩ := exists_inv' b'
  intro Φ hΦ Ψ hΨ
  refine LinearMap.eqOn_span' (f := L.flip (om (u, 1) Ψ)) (g := L.flip Ψ) ?_ hΦ
  rintro _ ⟨f', hf', φ', p1', p2', rfl⟩
  refine schA_le (LinearMap.eqLocus (L (pure f' φ') ∘ₛₗ om (u, 1)) (L (pure f' φ'))) (fun f φ p1 p2 => ?_) hΨ
  obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one v f p1 p2
  obtain ⟨T', t1', -, t3'⟩ := intersection_update_fsHerm_neg_one v f' p1' ((p2'.and hM'.std).mono fun _ h => h.1.trans h.2)
  have t2' : ∀ ψ ∈ SB _, T' ψ ∈ PolData B M' := fun ψ hψ => Submodule.subset_span ⟨f', hf', _, fun w => by
    by_cases hw : w = v
    · subst hw; rwa [Function.update_self]
    · rw [Function.update_of_ne hw]; exact p1' w, by
      filter_upwards [p2', eventually_cofinite_ne v] with w h hw using (Function.update_of_ne hw _ _).trans h, t1' ψ⟩
  let N : (Fv F v)ˣ →* ℂˣ := MonoidHom.toHomUnits ⟨⟨fun x => apow x ((d : ℂ) / 2), apow_one _⟩, fun x y => apow_mul x y _⟩
  have hN : ∀ x, ((ν * N⁻¹) x : ℂ) = ν x * (apow x ((d : ℂ) / 2))⁻¹ := fun x => by simp [N]
  have cj : ∀ {z : ℂ}, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun h => (Complex.inv_eq_conj h).symm
  have cj' : ∀ (x : (Fv F v)ˣ) (m : ℕ), starRingEnd ℂ (apow x ((m : ℂ) / 2)) = apow x ((m : ℂ) / 2) := fun x m => by
    obtain ⟨r, -, h⟩ := apow_real x m
    rw [h, Complex.conj_ofReal]
  let β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun a b => L (T' (j' b.1)) (T (j (star a.1)))) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) fun _ _ _ => by simp
  let g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀.1ᵀ (by rw [Matrix.det_transpose]; exact g₀.det_ne_zero)
  have key := locBil hL v e (ν * N⁻¹) (fun t ht h => hne (Units.ext ?_)) β (fun a b h₀ => ?_)
    ⟨_, sb_star (b.1 (p1 v))⟩ ⟨_, b'.1 (p1' v)⟩ g₁
  · have k2 := t3 _ _ (p1 v) _ (acts_of_reads hu j2 (p1 v)).2
    rw [omB_left, map_smul, map_smul, t1, Function.update_eq_self] at k2
    change L _ (T (j (star fun y => star (ι (φ v) (g₀.1ᵀ * y))))) = _ * L _ (T (j (star (star _)))) at key
    rw [star_star, j2 _ (p1 v), j2' _ (p1' v), t1', t1 (φ v), Function.update_eq_self, Function.update_eq_self, hN,
      show Matrix.GeneralLinearGroup.det g₁ = gdet g₀ from Units.ext (Matrix.det_transpose _), ← Pi.star_def, star_star] at key
    change L _ (om (u, 1) _) = _
    rw [k2, map_smulₛₗ, key, map_mul, cj (n1 _), cj', smul_eq_mul]
    have := apow_ne_zero (gdet g₀) ((d : ℂ) / 2)
    field_simp
  · obtain ⟨r, hr, e1⟩ := apow_real (unifAt v) d
    rw [hN, e1, mul_inv_eq_iff_eq_mul₀ (by exact_mod_cast hr.ne'), ← Complex.ofReal_mul] at h
    have := n1 (unifAt v)
    rw [h, Complex.norm_real, Real.norm_of_nonneg (mul_pos ht hr).le] at this
    rw [h, this]; rfl
  · obtain ⟨h, r1, r2, r3⟩ := hh h₀
    have a1 := j1 _ (sb_star a.2)
    have b1 := j1' _ b.2
    have k1 := t3 _ _ a1.1 _ (acts_of_reads r1 j2 a1.1).2
    have k2 := t3' _ _ b1.1 _ (acts_of_reads r2 j2' b1.1).2
    have k3 := r3 _ (t2' _ b1.1) _ (t2 _ a1.1)
    rw [k1, k2, a1.2, b1.2, omB_right, omB_right] at k3
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, cj (n2 _), cj'] at k3
    have hd : (d : ℂ) / 2 = (n : ℂ) / 2 + (n' : ℂ) / 2 := by
      have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      rw [← this]; push_cast; ring
    change L (T' (j' fun y => b.1 (y * h₀.1))) (T (j fun y => star a.1 (y * h₀.1))) = _ * L (T' (j' b.1)) (T (j (star a.1)))
    rw [← k3, hN, hν, hd, apow_add]
    have := apow_ne_zero (gdet h₀) ((n : ℂ) / 2)
    have := apow_ne_zero (gdet h₀) ((n' : ℂ) / 2)
    simp only [Units.val_div_eq_div_val]
    field_simp

end GlobalTheory.ThK.Dbl.TC

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global GlobalTheory.HeisSchA

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}


variable (F) in
def epsF : AF F := mk 0 1

theorem epsF_mul (t : AF F) : epsF F * t = mk 0 (p2 t) := Prod.ext (zero_mul _) (one_mul _)

theorem epsF_sq : epsF F * epsF F = epsF F := epsF_mul _

theorem evI_epsF (t : AF F) : evI F (epsF F * t) = 0 := by
  rw [epsF_mul]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem epsF_of {t : AF F} (h : evI F t = 0) : epsF F * t = t := by
  rw [epsF_mul]
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective ((map_zero _).trans h.symm)) rfl

theorem level (hψ : Continuous ψ) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) :
    ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, schr ψ (epsF F • w) Φ = Φ := by
  rw [sch_eq, schwartzBruhatPi_eq_cosetSpanPi] at h
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    have m := finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J (b i)
    have c := continuous_finPartPi (K := F) (ι := κ)
    have h1 : ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, ∀ i, finPartPi w.1 i ∈ idealFiniteAdeles J :=
      eventually_all.2 fun i => ((continuous_apply i).comp (c.comp continuous_fst)).continuousAt.preimage_mem_nhds
        ((isOpen_idealFiniteAdeles J).mem_nhds (zero_mem _))
    have h2 : ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, ∀ z ∈ tsupport (finiteTensor fun i => cosetIndicator J (b i)),
        finChar ψ (z ⬝ᵥ finPartPi w.2 + p2 ⅟(2 : AF F) * (finPartPi w.1 ⬝ᵥ finPartPi w.2)) = 1 :=
      m.2.isCompact.eventually_forall_of_forall_eventually fun z _ => by
        have := ((finChar_isLocallyConstant ψ hψ).comp_continuous (f := fun y : ((κ → AF F) × (κ → AF F)) × (κ → Af F) =>
          y.2 ⬝ᵥ finPartPi y.1.2 + p2 ⅟(2 : AF F) * (finPartPi y.1.1 ⬝ᵥ finPartPi y.1.2)) (by fun_prop)).eventually_eq (0, z)
        simpa [show finPartPi (0 : κ → AF F) = 0 from rfl] using this
    filter_upwards [h1, h2] with w h1 h2
    funext x
    have e1 : infPartPi (x + epsF F • w.1) = infPartPi x := funext fun i => by
      have := evI_epsF (w.1 i)
      exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _).trans ((congrArg _ this).trans (add_zero _))
    have e2 : finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi (x + epsF F • w.1)) =
        finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi x) := Finset.prod_congr rfl fun i _ => by
      beta_reduce
      rw [cosetIndicator_apply, cosetIndicator_apply,
        show finPartPi (x + epsF F • w.1) i - b i = finPartPi x i - b i + finPartPi w.1 i from by
          rw [sub_add_eq_add_sub]; exact congrArg (finPartPi x i + · - b i) (one_mul _)]
      simp only [AddSubgroup.add_mem_cancel_right _ (h1 i)]
    simp only [schr, schwartzBruhatTensorPi, Prod.smul_fst, Prod.smul_snd, e1, e2]
    by_cases h0 : finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi x) = 0
    · simp [h0]
    · rw [dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_smul, epsF_sq, smul_eq_mul, smul_eq_mul, mul_left_comm ⅟(2 : AF F),
        ← mul_add, epsF_mul, ← finChar_apply, map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
      exact (congrArg (· * _) (h2 _ (subset_tsupport _ h0))).trans (one_mul _)
  | zero => exact .of_forall fun w => funext fun x => mul_zero _
  | add G H _ _ hG hH =>
    filter_upwards [hG, hH] with w hG hH
    funext x
    exact (mul_add _ _ _).trans (congrArg₂ _ (congrFun hG x) (congrFun hH x))
  | smul c G _ hG =>
    filter_upwards [hG] with w hG
    funext x
    exact (mul_left_comm _ _ _).trans (congrArg _ (congrFun hG x))

theorem finite_values (hψ : IsStd ψ) {N : Set ((κ → AF F) × (κ → AF F))} (hN : N ∈ 𝓝 0) :
    ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧ ∀ Ψ : (κ → AF F) → ℂ, (∀ w ∈ N, schr ψ (epsF F • w) Ψ = Ψ) →
      ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) → ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0 := by
  obtain ⟨ξ, hξ, e⟩ := std_eq hψ
  obtain ⟨N₁, h₁, N₂, h₂, hN⟩ := mem_nhds_prod_iff.1 hN
  have cm : Continuous fun a : Af F => (mk 0 a : AF F) := continuous_const.prodMk continuous_id
  have : ∀ᶠ a : Af F in 𝓝 0, ∀ i, (Pi.single i (mk 0 a) : κ → AF F) ∈ N₂ := eventually_all.2 fun i =>
    ((continuous_single i).comp cm).continuousAt.preimage_mem_nhds (by
      rwa [Function.comp_apply, show (mk 0 0 : AF F) = 0 from rfl, Pi.single_zero])
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset this
  have hC := (isCompact_univ_pi fun _ : κ => isCompact_idealFiniteAdeles (traceDualIdeal F J)).image
    (f := fun y i => (mk 0 (algebraMap F (Af F) ξ⁻¹ * y i) : AF F))
    (continuous_pi fun i => cm.comp (continuous_const.mul (continuous_apply i)))
  obtain ⟨s, hs, hc⟩ := hC.elim_nhds_subcover (fun t => {y | y - t ∈ N₁}) fun t _ =>
    (continuous_sub_right t).continuousAt.preimage_mem_nhds (by rwa [sub_self])
  have hs' : ∀ y ∈ s, ∀ i, evI F (y i) = 0 := fun y hy i => by
    obtain ⟨z, -, rfl⟩ := hs y hy
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  refine ⟨s, hs', fun Ψ hΨ x hx h0 y hy => by_contra fun hn => ?_⟩
  have hx0 : epsF F • x = 0 := hx _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  refine (fun hm => ?_ : y ∈ _ → False) (hc ⟨fun i => algebraMap F (Af F) ξ * p2 (y i), fun i _ => ?_, ?_⟩)
  · obtain ⟨t, ht, hty⟩ := Set.mem_iUnion₂.1 hm
    have := congrFun (hΨ (y - t, 0) (hN ⟨hty, mem_of_mem_nhds h₂⟩)) (x + t)
    have e : epsF F • (y - t) = y - t := funext fun i => by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, epsF_of (hy i), epsF_of (hs' t ht i)]
    simp [schr, e, h0 t ht, hn] at this
  · refine (forall_finiteAdelicChar_mul_eq_one_iff J _).1 fun a ha => Circle.ext ?_
    have := congrFun (hΨ (0, Pi.single i (mk 0 a)) (hN ⟨mem_of_mem_nhds h₁, hJ ha i⟩)) (x + y)
    simp only [schr, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_dotProduct, mul_zero, add_zero] at this
    rw [mul_eq_right₀ hn, dotProduct_smul, ← smul_dotProduct, smul_add, hx0, zero_add, dotProduct_single, e] at this
    refine Eq.trans (congrArg (fun z => ((adelicChar F z : Circle) : ℂ)) (Prod.ext ?_ ?_)) this
    · exact (mul_zero _).symm.trans (congrArg _ (mul_zero _).symm)
    · show a * (algebraMap F (Af F) ξ * p2 (y i)) = algebraMap F (Af F) ξ * (1 * p2 (y i) * a)
      ring
  · funext i
    beta_reduce
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hξ, map_one, one_mul, ← epsF_mul, epsF_of (hy i)]

theorem finLevel : FinLevel := by
  intro F E _ _ _ _ _ σ B m n A Y hB κ _ dd K hK Φ hΦ
  have lin : ∀ (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      actB (cA σ) k (epsF F • u) = epsF F • actB (cA σ) k u := fun k u => Matrix.smul_mul _ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ∀ {α β : Type} [Finite α] [Finite β], IsModuleTopology (AF F) (Matrix α β (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (_ → _ → AE F E))
  have c : Continuous fun y : ((κ → AF F) × (κ → AF F)) × G2 σ Y => dd.e (actB (cA σ) y.2 (dd.e.symm y.1)) :=
    (IsModuleTopology.continuous_of_linearMap dd.e.toLinearMap).comp
      (((IsModuleTopology.continuous_of_linearMap dd.e.symm.toLinearMap).comp continuous_fst).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose)
  obtain ⟨s, hs, h⟩ := finite_values hB.std (hK.eventually_forall_of_forall_eventually
    (P := fun w k => schr B.ψ (epsF F • dd.e (actB (cA σ) k (dd.e.symm w))) Φ = Φ) fun k _ =>
      (c.tendsto' (0, k) 0 (by simp [actB])).eventually (level hB.std.1 hΦ))
  refine ⟨{u | epsF F • u = u ∧ ∀ k ∈ K, dd.rho B.ψ (actB (cA σ) k u) Φ = Φ}, fun u hu => ⟨fun i => ?_, fun i => ?_,
    fun k hk => ⟨by rw [← lin, hu.1], fun k' hk' => ?_⟩⟩, fun u hu => ?_, s, hs, fun Ψ hΨ => h Ψ fun w hw => ?_⟩
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · have := hu.2 _ (mul_mem hk' hk)
    simpa [actB, Matrix.mul_assoc] using this
  · simpa [actB] using hu.2 1 (one_mem _)
  · have := hΨ (epsF F • dd.e.symm w) ⟨by rw [smul_smul, epsF_sq], fun k hk => by
      rw [lin, Darboux.rho, map_smul]; exact hw k hk⟩
    rwa [Darboux.rho, map_smul, LinearEquiv.apply_symm_apply] at this

end GlobalTheory.ThK.Dbl

end
end
