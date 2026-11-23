module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.SplitSBProd

open Filter Topology

theorem eventually_pow_smul_mem {K M : Type} [Semiring K] [TopologicalSpace K] [AddCommMonoid M] [Module K M]
    [TopologicalSpace M] [ContinuousSMul K M] {c : K} (hc : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0))
    {C U : Set M} (hC : IsCompact C) (hU : U ∈ 𝓝 (0 : M)) : ∀ᶠ n in atTop, ∀ x ∈ C, c ^ n • x ∈ U := by
  have h1 : ∀ᶠ a in 𝓝 (0 : K), ∀ x ∈ C, a • x ∈ U := by
    apply hC.eventually_forall_of_forall_eventually
    intro x _
    have hc' : Continuous fun z : K × M => z.1 • z.2 := continuous_smul
    apply hc'.continuousAt.eventually_mem
    simpa using hU
  exact hc.eventually h1

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_pow_tendsto_zero : ∃ p : ℕ, 0 < p ∧ Tendsto (fun n : ℕ => (p : k) ^ n) atTop (𝓝 0) := by
  refine ⟨ringChar 𝓀[k], Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite 𝓀[k] _),
    GlobalTheory.LocalTraceSum.tendsto_pow ?_⟩
  have := (residue_eq_zero_iff_lt ((ringChar 𝓀[k] : ℕ) : 𝒪[k])).1
    (by rw [map_natCast]; exact ringChar.Nat.cast_ringChar)
  simpa using this

end Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_eq (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : WO S T) :
    (ofSplit q).down FS FT x = FT.γ * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr * FS.β := rfl

theorem down_add (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x y : WO S T) :
    (ofSplit q).down FS FT (x + y) = (ofSplit q).down FS FT x + (ofSplit q).down FS FT y := by
  rw [down_eq, down_eq, down_eq]
  have : ((x + y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr =
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr + (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr := by
    ext i j; simp
  rw [this, Matrix.mul_add, Matrix.add_mul]

theorem down_nsmul (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (n : ℕ) (x : WO S T) :
    (ofSplit q).down FS FT (n • x) = n • (ofSplit q).down FS FT x := by
  rw [down_eq, down_eq]
  have : ((n • x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr =
      n • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr := by
    ext i j; simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.SplitSBProd

namespace GlobalTheory.SplitSBProd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {S T : HSp D}

theorem exists_den_pr (q : GlobalTheory.FinPl.SplitPt D k) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ i j, (M : k) * q.pr (u i j) ∈ 𝒪[k] := by
  obtain ⟨M, hM, h⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS hT
  refine ⟨M, hM, fun u hu i j => ?_⟩
  have hfe : finPart D q.e ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, q.split.1])
  have hu' := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ q.e hfe u hu
  have h1 := h _ hu' i j
  have h2 : finPart D (q.e * ((M : AE D) * u i j)) ∈ intAE D := by
    apply GlobalTheory.PlaceDatum.finPart_mem_of_toEAf
    have e1 : q.e * ((M : AE D) * u i j) = (M : AE D) * (q.e • u) i j := by
      rw [Matrix.smul_apply, smul_eq_mul]; ring
    rw [e1, RingHom.map_mul, map_natCast]; exact h1
  have e2 : (M : k) * q.pr (u i j) = q.pr ((M : AE D) * u i j) := by rw [map_mul, map_natCast]
  rw [e2, q.int_iff, q.sec_pr]
  exact h2

theorem toEAf_mem_of_pr (q : GlobalTheory.FinPl.SplitPt D k) {x : AE D} (hx : q.pr x ∈ 𝒪[k]) :
    toEAf D (q.e * x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  apply GlobalTheory.IdemRes.toEAf_mem_of_finPart
  rw [← q.sec_pr]
  exact (q.int_iff _).1 hx

end GlobalTheory.SplitSBProd

namespace GlobalTheory.SplitSBProd



theorem isSBHalf_splitProd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ e : AE D, e * e = e → q.e * e = q.e → ∀ Ω : WO S T → ℂ, IsSBHalf (e - q.e) (latO S T ΛS ΛT fun _ => True) Ω → ∀ Φ : SB (Matrix Y Y' k), IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x then Φ.1 ((ofSplit q).down FS FT x) * Ω ((1 - q.e) • x) else 0) := by
  intro D k _ _ _ _ q Y Y' _ _ _ _ S T FS FT ΛS ΛT hS hT e he hqe Ω hΩ Φ
  obtain ⟨-, kΩ, hkΩ, hΩinv, hΩsup⟩ := hΩ
  obtain ⟨M, hM, hMden⟩ := exists_den_pr (S := S) (T := T) q hS.toIsLattice.fg hT.toIsLattice.fg
  obtain ⟨K₀, hK₀, hK₀mem⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hS hT
  obtain ⟨p, hp, hpt⟩ := exists_nat_pow_tendsto_zero (k := k)
  have hU := GlobalTheory.HalfCoordSB.eventually_invariant Φ.2.1 Φ.2.2
  have hCa : IsCompact ((fun A : Matrix (Fin T.rank) (Fin S.rank) k => FT.γ * A * FS.β) ''
      {A | ∀ i j, A i j ∈ 𝒪[k]}) :=
    GlobalTheory.SplitFlip.isCompact_intMatrix.image (by fun_prop)
  have hCb : IsCompact ((fun z : Matrix Y Y' k => FT.β * z * FS.γ) '' tsupport Φ.1) :=
    Φ.2.2.isCompact.image (by fun_prop)
  obtain ⟨N, hNa, hNb⟩ := ((eventually_pow_smul_mem hpt hCa hU).and
    (eventually_pow_smul_mem hpt hCb (GlobalTheory.SplitFlip.isOpen_intMatrix.mem_nhds fun i j => zero_mem _))).exists
  have hqe1 : e * q.e = q.e := by rw [mul_comm]; exact hqe
  have hqq : q.e * q.e = q.e := q.split.1
  have h1e : finPart D (1 - q.e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
    rw [← RingHom.map_mul, sub_mul, one_mul, mul_sub, mul_one, hqq, sub_self, sub_zero])

  have hinvΦ : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ (j : ℕ) x, Φ.1 (x + j • ((p ^ N * M) • (ofSplit q).down FS FT u)) = Φ.1 x := by
    intro u hu j
    have hw : ∀ y, Φ.1 (y + (p ^ N * M) • (ofSplit q).down FS FT u) = Φ.1 y := by
      have := hNa _ ⟨M • (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr, fun i j => by
        rw [Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul]; exact hMden u hu i j, rfl⟩
      dsimp only [Set.mem_setOf_eq] at this
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Matrix.mul_smul, Matrix.smul_mul, ← down_eq, ← mul_smul] at this
      exact this
    induction j with
    | zero => intro x; rw [zero_smul, add_zero]
    | succ j ih => intro x; rw [succ_nsmul, ← add_assoc, hw, ih]

  have hsupp : ∀ t : WO S T, Φ.1 ((ofSplit q).down FS FT t) ≠ 0 →
      K₀ • ((p ^ N) • (q.e • t)) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        (fun _ => True) := by
    intro t hΦt
    have hint := hNb _ ⟨_, subset_tsupport _ hΦt, by
      simp only [down_eq, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
      rw [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]⟩
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hint
    refine hK₀mem _ (Matrix.ext fun i j => ?_) fun i j => ?_
    · simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast,
        GlobalTheory.SplitScalar.infPart_splitIdem q.split, zero_mul, mul_zero, Matrix.zero_apply]
    · have hx : q.pr ((p ^ N) • t i j) ∈ 𝒪[k] := by
        have := hint i j
        rw [map_nsmul]; exact this
      have e1 : ((p ^ N) • (q.e • t)) i j = q.e * ((p ^ N) • t i j) := by
        change (p ^ N) • (q.e * t i j) = _
        rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]
      rw [e1]
      exact toEAf_mem_of_pr q hx
  refine ⟨fun t ht => ?_, kΩ * K₀ * (p ^ N * M), Nat.mul_pos (Nat.mul_pos hkΩ hK₀) (Nat.mul_pos (pow_pos hp N) hM), fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (if_neg h)
  · have hKu : IsHalf e ((kΩ * K₀ * (p ^ N * M)) • u) := GlobalTheory.HalfCoordSB.isHalf_nsmul hue _
    dsimp only
    by_cases ht : IsHalf e t
    · rw [if_pos ht, if_pos (GlobalTheory.HalfCoordSB.isHalf_add ht hKu)]
      have hΦe : Φ.1 ((ofSplit q).down FS FT (t + (kΩ * K₀ * (p ^ N * M)) • u)) =
          Φ.1 ((ofSplit q).down FS FT t) := by
        rw [down_add, down_nsmul, mul_smul]
        exact hinvΦ u hu _ _
      set v := (K₀ * (p ^ N * M)) • ((1 - q.e) • u) with hv
      have hvΛ : v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
        nsmul_mem (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1e u hu) _
      have hvh : IsHalf (e - q.e) v := fun i j => by
        rw [hv, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
        have hfac : (e - q.e) * (1 - q.e) = e - q.e := by
          rw [mul_sub, mul_one, sub_mul, hqe1, hqq, sub_self, sub_zero]
        have hx2 : (e - q.e) * u i j = (1 - q.e) * u i j := by rw [sub_mul, sub_mul, one_mul, hue i j]
        rw [mul_left_comm, ← mul_assoc (e - q.e), hfac, hx2]
      have hΩe : Ω ((1 - q.e) • (t + (kΩ * K₀ * (p ^ N * M)) • u)) = Ω ((1 - q.e) • t) := by
        have e2 : (1 - q.e) • (t + (kΩ * K₀ * (p ^ N * M)) • u) = (1 - q.e) • t + kΩ • v := by
          rw [hv, smul_add, smul_comm (1 - q.e) (kΩ * K₀ * (p ^ N * M)) u, mul_assoc kΩ, mul_smul]
        rw [e2]
        exact hΩinv v hvΛ hvh _
      rw [hΦe, hΩe]
    · have hn : ¬ IsHalf e (t + (kΩ * K₀ * (p ^ N * M)) • u) := fun h =>
        ht (by simpa using GlobalTheory.HalfCoordSB.isHalf_sub h hKu)
      rw [if_neg ht, if_neg hn]
  · dsimp only at ht
    have hh : IsHalf e t := by
      by_contra h
      exact ht (if_neg h)
    rw [if_pos hh] at ht
    have hΦt : Φ.1 ((ofSplit q).down FS FT t) ≠ 0 := left_ne_zero_of_mul ht
    have hΩt : Ω ((1 - q.e) • t) ≠ 0 := right_ne_zero_of_mul ht
    have e3 : t = q.e • t + (1 - q.e) • t := by rw [← add_smul, add_sub_cancel, one_smul]
    have e4 : kΩ * K₀ * (p ^ N * M) = (kΩ * M) * (K₀ * p ^ N) := by ring
    have e5 : kΩ * K₀ * (p ^ N * M) = (K₀ * (p ^ N * M)) * kΩ := by ring
    rw [e3, nsmul_add]
    refine add_mem ?_ ?_
    · rw [e4, mul_smul, mul_smul K₀]
      exact nsmul_mem (hsupp t hΦt) _
    · rw [e5, mul_smul]
      exact nsmul_mem (hΩsup _ hΩt) _

end GlobalTheory.SplitSBProd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem smul_mem_latMul (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (P : Pl D → Prop) (w : AE D)
    (hw : finPart D w ∈ intAE D) : ∀ y ∈ latMul S 𝔞 L P, w • y ∈ latMul S 𝔞 L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := AddMonoidHom.mk' (fun u => w • u) fun x y => smul_add w x y
  have main : latMul S 𝔞 L P ≤ (latMul S 𝔞 L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) := AddMonoidHom.mk'
      (fun y => fun i => GlobalTheory.LatticeStable.liftMul D (α ⊗ₜ[D.host.F] (a * x i)) y)
      fun y y' => funext fun i => (GlobalTheory.LatticeStable.liftMul D _).map_add y y'
    have hle : intAE D ≤ (latMul S 𝔞 L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, a, ha, o • x, L.smul_mem o hx, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · funext i
        change GlobalTheory.LatticeStable.liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finPart_e_int (q : SplitPt D k) : finPart D q.e ∈ intAE D := by
  have h := (q.int_iff 1).1 (one_mem _)
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  rwa [h1] at h

theorem e_mul_mem_latV (q : SplitPt D k) (S : HSp D) (L : Lat S) {s : Fin S.rank → D.host.E} (hs : s ∈ L) :
    (fun j => q.e * incA D (s j)) ∈ latV S L (· = q.v) := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hg : (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    AddSubgroup.subset_closure ⟨α, hα, fun u hu => h0 u hu, 1, rfl, s, hs, rfl⟩
  have he : q.e • (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    smul_mem_latMul S {1} L (· = q.v) q.e (finPart_e_int q) _ hg
  convert he using 1
  funext j
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]
  rw [Pi.smul_apply, smul_eq_mul, one_mul]
  have : pairA D.host.F 0 α ⊗ₜ[D.host.F] s j = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D (s j) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, ← mul_assoc, hee]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem rankOne_mem_latO (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) {y : Fin T.rank → AE D} (hy : y ∈ latA T LT P) :
    (Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
  let Φ : (Fin T.rank → AE D) →+ WO S T := AddMonoidHom.mk'
    (fun y => Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j))
    fun y y' => Matrix.ext fun i j => add_mul (y i) (y' i) _
  have main : latA T LT P ≤ (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩
    ext i j
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  exact main hy

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul (q : SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
open GlobalTheory.FinPl

theorem up_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → (ofSplit q).up FS FT x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT x hx
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S LS hS
  set u := (ofSplit q).up FS FT x with hu_def
  let z : Fin n → Y' → k := fun c => FS.γ *ᵥ (fun m => q.pr (incA D (s c m)))
  let y : Fin n → Fin T.rank → AE D := fun c i => ∑ m, u i m * incA D (s c m)
  have hz : ∀ c r, z c r ∈ 𝒪[k] := by
    intro c
    refine (hFS (z c)).2 ?_
    have : (fun i => q.sec ((FS.β *ᵥ z c) i)) = fun j => q.e * incA D (s c j) := by
      funext j
      simp only [z, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      exact q.sec_pr _
    rw [this]
    exact e_mul_mem_latV q S LS (hs c).1
  have hy : ∀ c, y c ∈ latA T LT (· = q.v) := by
    intro c
    rw [hU.2 T LT]
    have hint : ∀ r, (x *ᵥ z c) r ∈ 𝒪[k] := fun r =>
      Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hx r m) (hz c m)
    convert (hFT (x *ᵥ z c)).1 hint using 1
    funext i
    change ∑ m, q.sec ((FT.β * x * FS.γ) i m) * incA D (s c m) = _
    simp_rw [sec_mul]

    rw [← map_sum]
    congr 1
    simp only [z, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc]
    rfl
  have hdec : u = ∑ c, (Matrix.of fun i j => y c i * incA D (∑ l, star (s' c l) * S.gram l j) : WO S T) := by
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, y, Finset.sum_mul]
    rw [Finset.sum_comm]
    have key : ∀ m, ∑ c, u i m * incA D (s c m) * incA D (∑ l, star (s' c l) * S.gram l j) =
        u i m * incA D (if m = j then 1 else 0) := by
      intro m

      rw [← hss m j, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, mul_assoc]
    rw [Finset.sum_congr rfl fun m _ => key m]
    simp [apply_ite]
  rw [hdec]
  exact sum_mem fun c _ => rankOne_mem_latO S T LS LT _ (hs c).2 (hy c)

end GlobalTheory.UpMem
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SeeSaw.RedLev

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL F E n y := by
  simp [Formalism.L2.DIV.frGL]

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



theorem mul_moved (p : GlobalTheory.LocMod.Place D k) {π' : EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) (V : HSp D)
    (t x : GA D V) (β : GL (Fin V.rank) (Lev.EAf D)) (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Lev.finE V (t⁻¹ * x * t)) {M : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : GlobalTheory.LocMod.MovedTo p V t β M) :
    (mt V x).map p.π * M = M * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have h1 := hM (β.val.map f) (Matrix.ext fun i j => hf _)
  have h2 : (β.val.map f).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hf]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : Lev.finE V (t⁻¹ * x * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E _ y := by
    rw [← hy]
    exact frGL_mul (F := D.host.F) (E := D.host.E) β y
  have h4 : (mt V (t⁻¹ * x * t)).map p.π * β.val.map π' =
      β.val.map π' * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
    have h5 := congrArg (fun g : GL (Fin V.rank) (Lev.EAf D) => g.val.map π') h3
    simp only [Units.val_mul, Matrix.map_mul] at h5
    have h6 : (Lev.finE V (t⁻¹ * x * t)).val.map π' = (mt V (t⁻¹ * x * t)).map p.π := Matrix.ext fun i j => hπ _
    rw [h6] at h5
    exact h5
  have h7 : mt V x * mt V t = mt V t * mt V (t⁻¹ * x * t) := by
    rw [← GlobalTheory.MixModel.mt_mul, ← GlobalTheory.MixModel.mt_mul, mul_assoc, mul_inv_cancel_left]
  rw [← h1, ← Matrix.mul_assoc, ← Matrix.map_mul, h7, Matrix.map_mul, Matrix.mul_assoc, h4, Matrix.mul_assoc]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem conj_eq {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k n Y) (bas W : GL Y k) (σ : Fin n ≃ Y)
    (N : Matrix (Fin n) (Fin n) k)
    (h : F.β * W.val * F.γ * (F.β * bas.val).submatrix id σ = (F.β * bas.val).submatrix id σ * N) :
    (bas⁻¹ * W * bas).val.submatrix σ σ = N := by
  have h1 : ((bas⁻¹).val * F.γ).submatrix σ id * (F.β * bas.val).submatrix id σ = 1 := by
    change ((bas⁻¹).val * F.γ * (F.β * bas.val)).submatrix σ σ = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Units.inv_mul, Matrix.submatrix_one_equiv]
  rw [← Matrix.one_mul N, ← h1, Matrix.mul_assoc, ← h]
  change _ = ((bas⁻¹).val * F.γ * (F.β * W.val * F.γ * (F.β * bas.val))).submatrix σ σ
  congr 1
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ F.β bas.val, ← Matrix.mul_assoc F.γ F.β, F.γβ, Matrix.one_mul, Matrix.one_mul]

end

end GlobalTheory.SeeSaw.RedLev
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

noncomputable section
namespace GlobalTheory.LocMod

def IsLocFac (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (PP : Formalism.L2.DIV.Pl D.host.E) (c : WO S T →₀ ℂ)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (p : Place D k)
    (Y Y' : Type) (_ : Fintype Y) (_ : DecidableEq Y) (_ : Fintype Y') (_ : DecidableEq Y') (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) (Ξk : Matrix Y Y' k → ℂ),
    DenseRange p.pr ∧ Formalism.L2.NTheta.IsIdemAt p.e PP ∧
    (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) ∧
    Ξk ∈ SB (Matrix Y Y' k) ∧ p.IsCombAt ψ FS FT c Ξk ∧ ∀ γ, Ξ γ = Ξk (FT.γ * γ.map p.pr * FS.β)

end GlobalTheory.LocMod
end
end
