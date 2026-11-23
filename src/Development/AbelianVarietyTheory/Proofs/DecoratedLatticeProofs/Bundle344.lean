module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle167
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocComb

variable {D : D7}

theorem comb_add (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c + c') f = comb ψ S T c f + comb ψ S T c' f :=
  Finsupp.sum_add_index' (h := fun u (a : ℂ) => a • heisO ψ S T u f) (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, GlobalTheory.HeisComb.comb_eq_sum,
    Finsupp.sum_smul_index' (h := fun u (a : ℂ) => a • heisO ψ S T u f) fun _ => zero_smul _ _, Finsupp.smul_sum]
  simp only [smul_eq_mul, mul_smul]

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (zero_smul _ _),
    one_smul]

theorem heis_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {e : AE D} {y : WO S T} (hy : IsHalf e y) {c : WO S T →₀ ℂ}
    (hc : ∀ w ∈ c.support, IsHalf e w) :
    ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, IsHalf e w) ∧ ∀ f, comb ψ S T c' f = heisO ψ S T y (comb ψ S T c f) := by
  obtain ⟨c', h1, h2⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (Finsupp.single y 1) c
  refine ⟨c', fun w hw => ?_, fun f => by rw [h2, comb_single]⟩
  obtain ⟨x, hx, z, hz, rfl⟩ := h1 w hw
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx), add_comm]
  exact (Witness.half_add hy).2 (hc z hz)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']


omit [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] in
theorem trans_mem_SB {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (x : Matrix Y Y' k) :
    (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_const x), hΦ.2.comp_homeomorph (Homeomorph.addRight x)⟩


omit [DecidableEq Y] [DecidableEq Y'] in
theorem modul_mem_SB {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {Φ : Matrix Y Y' k → ℂ}
    (hΦ : Φ ∈ SB (Matrix Y Y' k)) (b : Matrix Y Y' k) : (fun t => Inhab.pairing ψ t b * Φ t) ∈ SB (Matrix Y Y' k) := by
  have hψ : IsLocallyConstant ψ := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    filter_upwards [((isOpen_cball d).preimage (continuous_sub_right x)).mem_nhds
      (show x - x ∈ cball d by simp [cball])] with z hz
    rw [← add_sub_cancel x z, AddChar.map_add_eq_mul, (hd d).2 le_rfl _ hz, mul_one]
  have h2 : IsLocallyConstant fun t : Matrix Y Y' k => Inhab.pairing ψ t b :=
    (hψ.comp_continuous (f := fun t : Matrix Y Y' k => ∑ r, ∑ q, b r q * t r q) (by fun_prop)).comp fun z : Circle => (z : ℂ)
  exact ⟨h2.mul hΦ.1, hΦ.2.mul_left⟩

theorem exists_comb : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ Φ₀ Φ : SB (Matrix Y Y' k), Φ₀ ≠ 0 → ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧ ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = comb ψ S T c (Tm Φ₀) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ Φ₀ Φ hΦ₀
  classical
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψk hcont hne
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := GlobalTheory.LocSympl.halves_at_split D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have half1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have half2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  let M : Submodule ℂ (SB (Matrix Y Y' k)) :=
    { carrier := {Ψ | ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧
        ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ψ = comb ψ S T c (Tm Φ₀)}
      zero_mem' := ⟨0, by simp, fun Tm _ => by simp [comb]⟩
      add_mem' := by
        rintro a b ⟨c, h1, h2⟩ ⟨c', h1', h2'⟩
        refine ⟨c + c', fun w hw => ?_, fun Tm h => by rw [map_add (f := _), comb_add, h2 Tm h, h2' Tm h]⟩
        exact (Finset.mem_union.1 (Finsupp.support_add hw)).elim (h1 w) (h1' w)
      smul_mem' := by
        rintro a b ⟨c, h1, h2⟩
        exact ⟨a • c, fun w hw => h1 w (Finsupp.support_smul hw), fun Tm h => by rw [map_smul, comb_smul, h2 Tm h]⟩ }
  have key : SB (Matrix Y Y' k) ≤ M.map (SB (Matrix Y Y' k)).subtype := by
    refine Inhab.sb_le hd ?_ ?_ Φ₀.2 (fun h => hΦ₀ (Subtype.ext h)) ⟨Φ₀, ⟨Finsupp.single 0 1, fun w hw => ?_, fun Tm _ => ?_⟩, rfl⟩
    · rintro x _ ⟨Ψ, ⟨c, h1, h2⟩, rfl⟩
      obtain ⟨c', h3, h4⟩ := heis_comb ψ S T (half1 _ (hup x).1) h1
      exact ⟨⟨_, trans_mem_SB Ψ.2 x⟩, ⟨c', h3, fun Tm h => by rw [h4, ← h2 Tm h]; exact h.trans x Ψ _ fun _ => rfl⟩, rfl⟩
    · rintro b _ ⟨Ψ, ⟨c, h1, h2⟩, rfl⟩
      obtain ⟨y, hy, hyb⟩ := hsurj b
      obtain ⟨c', h3, h4⟩ := heis_comb ψ S T (half2 _ hy) h1
      refine ⟨⟨_, modul_mem_SB hd Ψ.2 b⟩, ⟨c', h3, fun Tm h => ?_⟩, rfl⟩
      rw [h4, ← h2 Tm h]
      refine h.modul y hy Ψ _ fun t => ?_
      rw [hsymk t y hy, hyb t]
      rfl
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]
      exact fun i j => mul_zero _
    · rw [comb_single]
      funext w
      show _ = ψ (symplOH S T w 0) * Tm Φ₀ (w + 0)
      rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  obtain ⟨Ψ, hΨ, e⟩ := key Φ.2
  rw [← show Ψ = Φ from Subtype.ext e]
  exact hΨ

end GlobalTheory.LocComb

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Topology GlobalTheory.MixModel

namespace GlobalTheory.ContrModR

section SlopeTestRemainingChoices
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem incA_mul_ι (b : D.host.E) (x : k) : incA D b * p.ι x = p.ι (p.pr b * x) := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]
  rw [hm]
  change _ = p.ι (p.π (incA D b)) * p.ι x
  rw [p.ι_π, mul_assoc, mul_left_comm, Witness.e_ι]

theorem map_rat_mul_ι {a b c : Type} [Fintype b] (N : Matrix a b D.host.E) (M : Matrix b c k) :
    N.map (incA D) * M.map p.ι = (N.map p.pr * M).map p.ι := by
  ext i j

  simp [Matrix.mul_apply, incA_mul_ι, map_sum]

theorem map_pr_eq {a b : Type} (M : Matrix a b D.host.E) : M.map p.pr = M.map (Witness.prH p) := rfl

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem core_β {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) : F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) = B.o.iA.map p.pr * FA.β := by
  ext r a
  rw [← h.1 r a]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem core_qA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) :
    FA.γ * B.o.qA.map p.pr * F₀.β = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
  have hA : FA.γ * B.o.qA.map p.pr * (B.o.iA.map p.pr * FA.β) = 1 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (B.o.qA.map _), ← Matrix.map_mul, B.o.qA_iA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, FA.γβ]
  have hB : FA.γ * B.o.qA.map p.pr * B.o.iB.map p.pr = 0 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _),
      Matrix.mul_zero]
  have hc : ∀ r, F₀.β r (Sum.inr ()) = s * ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) r := by
    intro r
    rw [h.2 r, vecB, map_pr_eq]
    congr 1
    exact (RingHom.map_mulVec (Witness.prH p) B.o.iB B.ζ r)
  have hv : (FA.γ * B.o.qA.map p.pr) *ᵥ ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) = 0 := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  generalize (B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c)) = v at hc hv
  generalize FA.γ * B.o.qA.map p.pr = X at hA hv ⊢
  ext i (a | u)
  · have := congrFun (congrFun hA i) a
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, fromCols_apply_inl, ← this]
    simp only [h.1]
  · rw [Matrix.mul_apply, fromCols_apply_inr, Matrix.zero_apply]
    simp only [hc, mul_left_comm _ s, ← Finset.mul_sum]
    have h2 := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
    rw [h2, mul_zero]

end SlopeTestRemainingChoices

section Up
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)
variable {n n'' : Type} [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n'']

theorem up_fromRows {σ : ℕ} (B' : BesLev D σ) {s : k} (S : HSp D) (FA' : Frame k B'.A.rank n'')
    (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B' s FA' F₀')
    (x : Matrix n'' n k) :
    p.up FS F₀' (fromRows x (0 : Matrix Unit n k)) = (B'.o.resT S).symm (p.up FS FA' x, 0) := by
  have hx : fromRows x (0 : Matrix Unit n k) = fromRows (1 : Matrix n'' n'' k) (0 : Matrix Unit n'' k) * x := by
    rw [Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, map_rat_mul_ι, hx,
    ← Matrix.mul_assoc, core_β p B' FA' F₀' h]
  simp only [Matrix.mul_assoc]

theorem pA_up {σ : ℕ} (B' : BesLev D σ) {s : k} (S : HSp D) (FA' : Frame k B'.A.rank n'')
    (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B' s FA' F₀')
    (t : Matrix (n'' ⊕ Unit) n k) : B'.o.pA ⬝ p.up FS F₀' t = p.up FS FA' t.toRows₁ := by
  have hq : B'.o.qA.map p.pr * F₀'.β = fromCols FA'.β (0 : Matrix (Fin B'.A.rank) Unit k) := by
    have := congrArg (FA'.β * ·) (core_qA p B' FA' F₀' h)
    simp only [← Matrix.mul_assoc, FA'.βγ, Matrix.one_mul] at this
    rw [this, Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [Place.up, Place.up, OrthDec.pA, rat, map_rat_mul_ι, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq]
  conv_lhs => rw [← fromRows_toRows t]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

end Up

section Pass
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ)

theorem symplOH_zero_r {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have : hO S T x 0 = 0 := by simp [hO]
  simp [symplOH, symplO, this]

theorem heis_pass {V A L : HSp D} (o : OrthDec V A L) (S : HSp D) (f : WO S V → ℂ) (b v : WO S A) (z : WO S L) :
    heisO ψ S V ((o.resT S).symm (b, 0)) f ((o.resT S).symm (v, z)) =
      ψ (symplOH S A v b) * f ((o.resT S).symm (v + b, z)) := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

end Pass

end GlobalTheory.ContrModR

namespace GlobalTheory.ContrModR

theorem contr_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B' s FA' F₀' → ∀ (T₂ : SB (Matrix (n'' ⊕ Unit) n k) →ₗ[ℂ] (WO S B'.V₀ → ℂ)), p.IsModel ψ FS F₀' T₂ → ∀ (φ₀ : SB (n → k)) (Ξ₁ : WO B.V₀ S → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → ∀ (u : WO B.A S) (T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ)), (∀ Ξ₂ v, T Ξ₂ v = GlobalTheory.Unf.contr l S vL Ξ₁ (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Ξ₂)) u v) → p.IsModel ψ FS FA' T := by
  intro D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n'' _ _ _ _ FS FA' F₀' hcore T₂ hT₂ φ₀ Ξ₁ hΞ₁ u T hT

  have pass : ∀ (b : WO S B'.A) (Φ Φ' : SB (Matrix n'' n k)),
      T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ') =
        heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ)) →
      T Φ' = heisO ψ S B'.A b (T Φ) := by
    intro b Φ Φ' e
    funext v
    rw [hT Φ' v, e]
    change _ = ψ (symplOH S B'.A v b) * T Φ (v + b)
    rw [hT Φ (v + b)]
    unfold GlobalTheory.Unf.contr
    rw [← integral_const_mul]
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    rw [heis_pass]
    ring
  refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
  ·
    haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
    haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
      ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨C₁, hC₁⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ hΞ₁
    have hc : Continuous fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) :=
      hΞ₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp
        (Continuous.prodMk continuous_const (GlobalTheory.ContractionLocal.continuous_kappa l S)))
    have hint : Integrable (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) (vL.μ.restrict vL.𝓕) :=
      (integrable_const C₁).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₁ _)
    have h := GlobalTheory.SuperposT.superpos_target D ψ hψ B'.V₀ B'.A B'.L S B'.o (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ))
      (hT₂.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) id (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w)))
      measurable_id hint
    convert h using 1
    funext v
    rw [hT]
    unfold GlobalTheory.Unf.contr
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    simp only [id]
    ring
  ·
    refine pass (p.up FS FA' x) Φ Φ' ?_
    rw [← up_fromRows p B' S FA' F₀' FS hcore x]
    refine hT₂.trans _ _ _ fun t => ?_
    have h1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
      ext i j; simp [Matrix.toRows₁]
    have h2 : (t + fromRows x (0 : Matrix Unit n k)) (Sum.inr ()) = t (Sum.inr ()) := by
      funext j; simp
    simp only [GlobalTheory.ContractionLocal.rowTens_apply, e, h1, h2]
  ·
    refine pass y Φ Φ' (hT₂.modul _ ?_ _ _ fun t => ?_)
    · intro i j
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [mul_left_comm, hy c j]
    · simp only [GlobalTheory.ContractionLocal.rowTens_apply, e]
      rw [B'.o.symplO_resT S (p.up FS F₀' t), AddEquiv.apply_symm_apply]
      rw [OrthDec.resT_apply B'.o S (p.up FS F₀' t)]
      simp only
      rw [pA_up p B' S FA' F₀' FS hcore t]
      have : symplO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0 := by
        have h0 : hO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0 := by simp [hO]
        simp [symplO, h0]
      simp only [this, add_zero]
      ring

end GlobalTheory.ContrModR

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
open scoped GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineRowFrame

variable {D : D7}

theorem half_mul {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (v : Mx D m n) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu i]

theorem mul_half {e : AE D} {l m n : ℕ} (u : Mx D l m) {v : Mx D m n} (hv : IsHalf e v) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_left_comm, hv a j]

theorem adj_half {e : AE D} {m n : ℕ} {u : Mx D m n} (hu : IsHalf e u) : IsHalf (cA D e) (adj u) := fun i j => by
  change cA D e * cA D (u j i) = cA D (u j i)
  rw [← map_mul, hu j i]

theorem ofAdj_half {e : AE D} (S T : HSp D) {z : Mx D S.rank T.rank} (hz : IsHalf e z) :
    IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) := fun i j => by
  have h := mul_half (giA T) (half_mul (adj_half hz) (gA S)) i j
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, Matrix.smul_apply, smul_eq_mul, mul_left_comm, h]

theorem xi_mul_hO (S T : HSp D) (x : WO S T) (z : Mx D S.rank T.rank) :
    incA D D.host.xi0 * hO S T x (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) = (z ⬝ x).trace := by
  conv_rhs => rw [← GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj S T z]
  rw [hO_eq_trace, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc,
    Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem incA_mul_ι (a : D.host.E) (x : k) : incA D a * p.ι x = p.ι (p.pr a * x) := by
  conv_rhs => rw [← p.π_ι x, Place.pr, ← map_mul, p.ι_π, mul_left_comm, Witness.e_ι]

theorem pr_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) (r : Fin m) :
    p.pr ((M *ᵥ v) r) = ∑ a, p.pr (M r a) * p.pr (v a) := by

  simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem line_row : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ u₀ : n → k, ∃ x : WO S B'.L, p.up FS F₀' (fromRows 0 (Matrix.of fun _ => u₀)) = (B'.o.resT S).symm (0, x) ∧ IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) ∧ ∀ t : Matrix n (n' ⊕ Unit) k, ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (0, l.κ S x))) = ((ψk (-(u₀ ⬝ᵥ fun r => t r (Sum.inr ()))) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h₀ h₀' u₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  obtain ⟨w, hw⟩ : ∃ w, w = u₀ ᵥ* FS.γ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : WO S B'.L, ∀ a c, x a c = p.ι (s * p.xi * p.pr (B'.ζ a) * w c) :=
    ⟨Matrix.of fun a c => p.ι (s * p.xi * p.pr (B'.ζ a) * w c), fun _ _ => rfl⟩
  have hxh : IsHalf p.e x := fun a c => by rw [hx, Witness.e_ι]
  have hy : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  have hh : IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) := by
    rw [hy]
    exact half_mul (ofAdj_half B.L S (mul_half _ hxh)) _
  refine ⟨x, ?_, hh, fun t => ?_⟩
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    ext r c
    have e1 : (F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c = s * p.xi * p.pr (vecB B'.o B'.ζ r) * w c := by
      rw [Matrix.mul_assoc, fromRows_mul, Matrix.zero_mul, Matrix.mul_apply, Fintype.sum_sum_type, ← h₀'.2 r, hw]
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    change p.ι ((F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c) = _

    rw [e1, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx]
    change _ = incA D (B'.o.iB r a) * _
    rw [incA_mul_ι]
    congr 1
    ring
  · rw [(GlobalTheory.LocSympl.halves_at_split D k p _ _ B.V₀ S F₀ FS ψ ψk hk).2.2.2.1 t _ hh]
    congr 2
    rw [B.o.hO_resS, AddEquiv.apply_symm_apply, hO_eq_trace B.A, adj_zero, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.trace_zero, zero_add]
    refine mul_left_cancel₀ hxi ?_
    have e2 : ∀ a c, p.π (((rat l.τ : Mx D B.L.rank B'.L.rank) ⬝ x) a c) = -(s * p.xi * w c) * p.pr (B.ζ a) := fun a c => by
      have h1 := pr_mulVec p l.τ B'.ζ a
      rw [l.map, Pi.neg_apply, Place.pr, map_neg, map_neg] at h1

      rw [Place.pr, neg_mul, ← mul_neg, h1, Matrix.mul_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, hx, p.π_ι]
      change p.pr (l.τ a b) * _ = _
      ring
    have e3 : ∀ c a, p.π ((p.up F₀ FS t ⬝ B.o.jB) c a) = ∑ r, (FS.β * t * F₀.γ) c r * p.pr (B.o.iB r a) := fun c a => by

      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (p.π_ι _)
    have e4 : ∀ c, ∑ r, (FS.β * t * F₀.γ) c r * F₀.β r (Sum.inr ()) = (FS.β * t) c (Sum.inr ()) := fun c => by
      rw [← Matrix.mul_apply, Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
    have e5 : ∑ c, w c * (FS.β * t) c (Sum.inr ()) = u₀ ⬝ᵥ fun r => t r (Sum.inr ()) := by
      change (w ᵥ* (FS.β * t)) (Sum.inr ()) = (u₀ ᵥ* t) (Sum.inr ())
      rw [hw, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, FS.γβ, Matrix.one_mul]
    change p.π (incA D D.host.xi0) * p.π (hO B.L S (p.up F₀ FS t ⬝ B.o.jB) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S _)) = _

    rw [← map_mul, xi_mul_hO, Matrix.trace_mul_comm, ← e5, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_

    rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, ← e4,
    Finset.sum_congr rfl fun a _ => (p.π.map_mul _ _).trans (congrArg₂ (· * ·) (e3 c a) (e2 a c))]
    generalize FS.β * t * F₀.γ = M
    simp only [h₀.2, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.LineRowFrame
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  first | exact @GlobalTheory.LocMod.normalFrames_exist | exact GlobalTheory.LocMod.normalFrames_exist | (intros; apply GlobalTheory.LocMod.normalFrames_exist <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.heisenberg_frame_half_inverse : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → (∀ x, IsHalf p.e (p.up FS FT x) ∧ p.down FS FT (p.up FS FT x) = x) ∧ (∀ z : WO S T, IsHalf p.e z → p.up FS FT (p.down FS FT z) = z) ∧ (∀ x y, symplO S T (p.up FS FT x) (p.up FS FT y) = 0) ∧ (∀ t (y : WO S T), IsHalf (cA D p.e) y → ψ (symplO S T (p.up FS FT t) y) = ψk (p.π (hO S T (p.up FS FT t) y))) ∧ ∀ b : Matrix Y Y' k, ∃ y : WO S T, IsHalf (cA D p.e) y ∧ ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  first | exact @GlobalTheory.LocSympl.halves_at_split | exact GlobalTheory.LocSympl.halves_at_split | (intros; apply GlobalTheory.LocSympl.halves_at_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.mem_flagUnipotentRadical_of_besselNormalFrameLocal : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → g ∈ flagN B.d := by
  first | exact @GlobalTheory.LocFlag.mem_flagN | exact GlobalTheory.LocFlag.mem_flagN | (intros; apply GlobalTheory.LocFlag.mem_flagN <;> assumption)
end
