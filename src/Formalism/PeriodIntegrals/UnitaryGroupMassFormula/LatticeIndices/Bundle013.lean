module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle011
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl
open scoped TensorProduct

section Reindex

variable {K : Type} [Field K] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {m : ℕ}

end Reindex

section Split

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

def cmp1 (g : HA R σ J) : Matrix (Fin n) (Fin n) R :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (fun t => (θ t).1)

def cmp2 (g : HA R σ J) : Matrix (Fin n) (Fin n) R :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (fun t => (θ t).2)

def jm1 : Matrix (Fin n) (Fin n) R := (JR R J).map (fun t => (θ t).1)

theorem cmp_unit (hθ : ∀ t, θ (sigR R σ t) = (θ t).swap) (g : HA R σ J) :
    (cmp2 σ J θ g)ᵀ * jm1 J θ * cmp1 σ J θ g = jm1 J θ := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = JR R J := g.2
  let f1 : R ⊗[F] E →+* R := (RingHom.fst R R).comp θ.toRingEquiv.toRingHom
  have h1 := congrArg (fun M => Matrix.map M f1) hg
  simp only [Matrix.map_mul] at h1
  have e1 : (Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))).map f1 = (cmp2 σ J θ g)ᵀ := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
    show (θ (sigR R σ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i))).1 = (θ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i)).2
    rw [hθ]
    rfl
  rw [e1] at h1
  exact h1

private theorem mem_span_image_iff_pr1_pr2_mem_span {ι : Type} [Fintype ι] (s : Set ι) (u : ι → Fin n → R ⊗[F] E)
    (w : Fin n → R ⊗[F] E) :
    w ∈ Submodule.span (R ⊗[F] E) (u '' s) ↔
      pr1 θ w ∈ Submodule.span R ((fun i => pr1 θ (u i)) '' s) ∧
      pr2 θ w ∈ Submodule.span R ((fun i => pr2 θ (u i)) '' s) := by
  classical
  have h1 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr1 θ (c • v) = (θ c).1 • pr1 θ v := by
    intro c v
    funext i
    show (θ (c * v i)).1 = (θ c).1 * (θ (v i)).1
    rw [map_mul]
    rfl
  have h2 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr2 θ (c • v) = (θ c).2 • pr2 θ v := by
    intro c v
    funext i
    show (θ (c * v i)).2 = (θ c).2 * (θ (v i)).2
    rw [map_mul]
    rfl
  have hinj : ∀ x y : Fin n → R ⊗[F] E, pr1 θ x = pr1 θ y → pr2 θ x = pr2 θ y → x = y := by
    intro x y hx hy
    funext i
    apply θ.injective
    exact Prod.ext (congrFun hx i) (congrFun hy i)
  simp only [Set.image_eq_range, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨⟨fun i => (θ (c i)).1, ?_⟩, ⟨fun i => (θ (c i)).2, ?_⟩⟩
    · rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (h1 (c i) (u ↑i)).symm
    · rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (h2 (c i) (u ↑i)).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨fun i => θ.symm (a i, b i), ?_⟩
    apply hinj
    · rw [map_sum]
      simp only [h1, AlgEquiv.apply_symm_apply]
      exact ha
    · rw [map_sum]
      simp only [h2, AlgEquiv.apply_symm_apply]
      exact hb

private theorem pr1_lin_eq_cmp1_mulVec (g : HA R σ J) (v : Fin n → R ⊗[F] E) :
    pr1 θ (lin R σ J g v) = cmp1 σ J θ g *ᵥ pr1 θ v := by
  have hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr1 θ w k = (θ (w k)).1 := fun _ _ => rfl
  funext i

  simp only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp1, Matrix.map_apply,
  map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]

private theorem pr2_lin_eq_cmp2_mulVec (g : HA R σ J) (v : Fin n → R ⊗[F] E) :
    pr2 θ (lin R σ J g v) = cmp2 σ J θ g *ᵥ pr2 θ v := by
  have hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr2 θ w k = (θ (w k)).2 := fun _ _ => rfl
  funext i

  simp only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp2, Matrix.map_apply,
  map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]

theorem mem_Ssub_iff_flagC {r : ℕ} (P : Frame E n r) (g : HA R σ J) :
    g ∈ Ssub R σ J P ↔ FlagC (cmp1 σ J θ g) (fun b => pr1 θ (ratV (F := F) R (F0 P b))) ∧
      FlagC (cmp2 σ J θ g) (fun b => pr2 θ (ratV (F := F) R (F0 P b))) := by
  have hm : g ∈ Ssub R σ J P ↔ UniC R σ J (F0 P) g := Iff.rfl
  rw [hm]
  unfold UniC FlagC
  rw [← forall_and]
  apply forall_congr'
  intro b
  show lin R σ J g (ratV (F := F) R (F0 P b)) - ratV (F := F) R (F0 P b) ∈ spanR (F := F) R (F0 P) {a | a < b} ↔
    (cmp1 σ J θ g *ᵥ pr1 θ (ratV (F := F) R (F0 P b)) - pr1 θ (ratV (F := F) R (F0 P b)) ∈
      Submodule.span R ((fun c => pr1 θ (ratV (F := F) R (F0 P c))) '' {a | a < b})) ∧
    (cmp2 σ J θ g *ᵥ pr2 θ (ratV (F := F) R (F0 P b)) - pr2 θ (ratV (F := F) R (F0 P b)) ∈
      Submodule.span R ((fun c => pr2 θ (ratV (F := F) R (F0 P c))) '' {a | a < b}))
  unfold spanR
  rw [mem_span_image_iff_pr1_pr2_mem_span, map_sub, map_sub, pr1_lin_eq_cmp1_mulVec, pr2_lin_eq_cmp2_mulVec]

end Split

end MassDataIdxStIm
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_inModP_Bg (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    InModP X p X.B.g S y ↔ InModP X p (gOf p) S y := by
  unfold InModP
  rw [imA_span_Bg X p]

theorem imA_OEp_one (p : TypX X) : (1 : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) ∈ OEp X p :=
  ⟨1, Subring.one_mem _, map_one _⟩

theorem imA_OEp_sub (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s - t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a - b, Subring.sub_mem _ ha hb, map_sub _ _ _⟩

abbrev epsP (p : TypX X) : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E := PI.FinKW.psiV X.B.I p.1 X.ew

theorem imA_eps_mem (p : TypX X) : epsP X p ∈ OEp X p := ⟨X.ew, X.ew_int, rfl⟩

theorem imA_eps_idem (p : TypX X) : epsP X p * epsP X p = epsP X p := by
  unfold epsP
  rw [← map_mul, X.ew_idem]

private theorem latLoc_ringOfIntegers_incl (p : TypX X) (x : 𝓞 X.B.I.E) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((1 : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  unfold latLoc at hu ⊢
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    refine Submodule.subset_span ⟨x • l, X.B.I.L.smul_mem x hl, ?_⟩
    funext i
    simp [ratV, inclR, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

private theorem latLoc_adicIntegers_incl (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h : ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u = c • u := by
    funext i
    simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c hu

theorem imA_lat_OEp (p : TypX X) {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    t • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have key : ∀ b ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E, ∀ w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)),
      PI.FinKW.psiV X.B.I p.1 b • w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro b hb
    unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at hb
    induction hb using Subring.closure_induction with
    | mem z hz =>
      intro w hw
      rcases hz with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
      · obtain ⟨x, rfl⟩ := RingHom.mem_range.mp he
        convert latLoc_ringOfIntegers_incl X p x hw using 2
        simp [PI.FinKW.psiV]
      · have hy' : ∀ v, y v ∈ v.adicCompletionIntegers X.B.I.F := hy
        convert latLoc_adicIntegers_incl X p ⟨y p.1, hy' p.1⟩ hw using 2
        simp [PI.FinKW.psiV] <;> rfl
    | zero => intro w _; simp
    | one => intro w hw; simpa using hw
    | add a b _ _ ha hb => intro w hw; rw [map_add (f := _), add_smul]; exact add_mem (ha w hw) (hb w hw)
    | neg a _ ha => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (ha w hw)
    | mul a b _ _ ha hb => intro w hw; rw [map_mul, mul_smul]; exact ha _ (hb w hw)
  obtain ⟨a, ha, rfl⟩ := ht
  exact key a ha u hu

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] {r k : ℕ}

theorem frame_mem_sG (g1 Q : GL (Idx r k) K) (g2 J1 : Matrix (Idx r k) (Idx r k) K) (hJ : IsUnit J1.det)
    (hU : g2ᵀ * J1 * (g1 : Matrix (Idx r k) (Idx r k) K) = J1)
    (y1 y2 : Fin (r + 1) → Idx r k → K) (l : Fin (r + 1) → K) (hl : ∀ b, l b ≠ 0)
    (hy1 : ∀ b, ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) *ᵥ y1 b = Pi.single (pe b) 1)
    (hy2 : ∀ b, (Q : Matrix (Idx r k) (Idx r k) K)ᵀ *ᵥ (J1ᵀ *ᵥ y2 b) = l b • Pi.single (pf b) 1) :
    (FlagC (g1 : Matrix (Idx r k) (Idx r k) K) y1 ∧ FlagC g2 y2) ↔ Q⁻¹ * g1 * Q ∈ sG K r k := by
  set G1 : Matrix (Idx r k) (Idx r k) K := (g1 : Matrix (Idx r k) (Idx r k) K) with hG1
  set G1i : Matrix (Idx r k) (Idx r k) K := ((g1⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hG1i
  set Qm : Matrix (Idx r k) (Idx r k) K := (Q : Matrix (Idx r k) (Idx r k) K) with hQm
  set Qi : Matrix (Idx r k) (Idx r k) K := ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hQi
  have e1 : G1 * G1i = 1 := by rw [hG1, hG1i, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1' : G1i * G1 = 1 := by rw [hG1, hG1i, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have eQ : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have eQ' : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJt : IsUnit J1ᵀ.det := by rw [Matrix.det_transpose]; exact hJ
  have eJ : J1ᵀ⁻¹ * J1ᵀ = 1 := Matrix.nonsing_inv_mul _ hJt
  have eJ' : J1ᵀ * J1ᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJt
  have hS : ((Q⁻¹ * g1 * Q : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1 * Qm := by
    simp [hQi, hG1, hQm, Units.val_mul]
  have hSi : (((Q⁻¹ * g1 * Q)⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1i * Qm := by
    have : (Q⁻¹ * g1 * Q)⁻¹ = Q⁻¹ * g1⁻¹ * Q := by group
    rw [this]
    simp [hQi, hG1i, hQm, Units.val_mul]

  have hT : J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ := by
    have hUt : G1ᵀ * J1ᵀ * g2 = J1ᵀ := by
      have := congrArg Matrix.transpose hU
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    have hit : G1iᵀ * G1ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ * (G1ᵀ * J1ᵀ * g2) * J1ᵀ⁻¹ := by
          rw [← Matrix.mul_assoc G1iᵀ, ← Matrix.mul_assoc G1iᵀ, hit, Matrix.one_mul]
      _ = G1iᵀ := by rw [hUt, Matrix.mul_assoc, eJ', Matrix.mul_one]
  rw [mem_sG_iff_flagC, hS, hSi]
  refine and_congr ?_ ?_
  · rw [← flagC_conj Qi Qm G1 eQ eQ' y1]
    exact Iff.of_eq (congrArg _ (funext hy1))
  · rw [← flagC_conj J1ᵀ J1ᵀ⁻¹ g2 eJ eJ' y2, hT]
    have eQt : Qiᵀ * Qmᵀ = 1 := by rw [← Matrix.transpose_mul, eQ, Matrix.transpose_one]
    have eQt' : Qmᵀ * Qiᵀ = 1 := by rw [← Matrix.transpose_mul, eQ', Matrix.transpose_one]
    rw [← flagC_conj Qmᵀ Qiᵀ G1iᵀ eQt eQt' _]
    have hv : (fun b => Qmᵀ *ᵥ (J1ᵀ *ᵥ y2 b)) = fun b => l b • Pi.single (pf (k := k) b) (1 : K) := funext hy2
    rw [hv, flagC_smul _ l hl]
    have hm : Qmᵀ * G1iᵀ * Qiᵀ = (Qi * G1i * Qm)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm]

end MassDataIdxStIm
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

section Gen

variable {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]

theorem dual_basis_iff (P : GL n K) (J : Matrix n n K) (z : n → K) :
    (∀ y : n → K, (∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O) → z ⬝ᵥ (J *ᵥ y) ∈ O) ↔
      ∀ i, ((Matrix.transpose (P : Matrix n n K) * Matrix.transpose J) *ᵥ z) i ∈ O := by
  have key : ∀ c : n → K, z ⬝ᵥ (J *ᵥ ((P : Matrix n n K) *ᵥ c)) =
      ((Matrix.transpose (P : Matrix n n K) * Matrix.transpose J) *ᵥ z) ⬝ᵥ c := by
    intro c
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_mul]
  have hPP : ∀ c : n → K, ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ ((P : Matrix n n K) *ᵥ c) = c := by
    intro c
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hPP' : ∀ y : n → K, (P : Matrix n n K) *ᵥ (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro h i
    have h1 := h ((P : Matrix n n K) *ᵥ Pi.single i 1) (by
      intro j
      rw [hPP]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij])
    rw [key, dotProduct_single_one] at h1
    exact h1
  · intro h y hy
    rw [← hPP' y, key]
    exact sum_mem fun i _ => mul_mem (h i) (hy i)

end Gen

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

abbrev OpX : ValuationSubring (FpX X p) := p.1.adicCompletionIntegers X.B.I.F

def iota1 : X.B.I.E →+* FpX X p := (th1 X p θ).comp (inclR (FpX X p))

def iota2 : X.B.I.E →+* FpX X p := (th2 X p θ).comp (inclR (FpX X p))

def Mlat1 : Submodule (OpX X p) (Fin X.B.I.n → FpX X p) :=
  Submodule.span (OpX X p) ((fun l : Fin X.B.I.n → X.B.I.E => fun j => iota1 X p θ (l j)) ''
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))

def Mlat2 : Submodule (OpX X p) (Fin X.B.I.n → FpX X p) :=
  Submodule.span (OpX X p) ((fun l : Fin X.B.I.n → X.B.I.E => fun j => iota2 X p θ (l j)) ''
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))

def LatSplitP : Prop :=
  ∀ x : Fin X.B.I.n → TpX X p, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    (fun j => th1 X p θ (x j)) ∈ Mlat1 X p θ ∧ (fun j => th2 X p θ (x j)) ∈ Mlat2 X p θ

def LatFreeP : Prop :=
  ∃ P : GL (Fin X.B.I.n) (FpX X p), ∀ y, y ∈ Mlat1 X p θ ↔
    ∀ i, (((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *ᵥ y) i ∈ OpX X p

def LatDualP : Prop :=
  ∀ z, z ∈ Mlat2 X p θ ↔ ∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p

theorem latBasis_of (hS : LatSplitP X p θ) (hF : LatFreeP X p θ) (hD : LatDualP X p θ) :
    ∃ P, LatBasis X p θ P := by
  obtain ⟨P, hP⟩ := hF
  refine ⟨P, fun x => ?_⟩
  rw [hS x, hD, hP]
  refine and_congr Iff.rfl ?_
  rw [← dual_basis_iff (OpX X p) P (J1 X p θ)]
  exact ⟨fun h y hy => h y ((hP y).2 hy), fun h y hy => h y ((hP y).1 hy)⟩

theorem latBasisAll_of
    (hS : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatSplitP X p θ)
    (hF : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatFreeP X p θ)
    (hD : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatDualP X p θ) :
    LatBasisAll X p := fun θ hθ => latBasis_of X p θ (hS θ hθ) (hF θ hθ) (hD θ hθ)

end Loc

end MassDataIdxSteps
end
end
