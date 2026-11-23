module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle003
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private noncomputable def UpperTheory.V.Pa.phDecD {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) : S.Bh →+ S.F where
  toFun b := Φ (b • y) - S.rF b * Φ y
  map_zero' := by simp
  map_add' b b' := by rw [add_smul, map_add (f := _), map_add (f := _)]; ring

private theorem UpperTheory.V.Pa.phDecD_apply {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) (b : S.Bh) :
    phDecD S Φ y b = Φ (b • y) - S.rF b * Φ y := rfl

private theorem UpperTheory.V.Pa.phDecD_mem {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (hΦ : Φ ∈ S.Ph)
    (y : S.U.N) : phDecD S Φ y ∈ S.Tp := by
  obtain ⟨h1, h2⟩ := hΦ
  have hm : ∀ q ∈ maximalIdeal S.Bh, S.rF q = 0 := fun q hq => by
    rw [← S.rF_ker] at hq; exact hq
  have dec : ∀ b : S.Bh, ∃ (o : S.OO) (q : S.Bh), q ∈ maximalIdeal S.Bh ∧ b = algebraMap S.OO S.Bh o + q := by
    intro b
    obtain ⟨o, ho⟩ := S.oo_surj (S.rF b)
    refine ⟨o, b - algebraMap S.OO S.Bh o, ?_, by ring⟩
    rw [← S.rF_ker, RingHom.mem_ker, map_sub, ← ho]
    simp
  refine ⟨fun b b' => ?_, fun o => ?_, fun b hb => ?_⟩
  · obtain ⟨o, q, hq, rfl⟩ := dec b
    obtain ⟨o', q', hq', rfl⟩ := dec b'
    have hqq : q * q' ∈ S.J2 := by
      refine Ideal.mem_sup_left (Ideal.mem_sup_right ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul hq hq'
    have e : ((algebraMap S.OO S.Bh o + q) * (algebraMap S.OO S.Bh o' + q')) • y =
        algebraMap S.OO S.Bh o • (algebraMap S.OO S.Bh o' • y) + algebraMap S.OO S.Bh o • (q' • y) +
          algebraMap S.OO S.Bh o' • (q • y) + (q * q') • y := by
      simp only [smul_smul, ← add_smul]
      congr 1
      ring
    simp only [phDecD_apply]
    rw [e]
    simp only [add_smul, map_add (f := _), map_mul, h1, h2 _ hqq, hm q hq, hm q' hq']
    ring
  · rw [phDecD_apply, h1, sub_self]
  · have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
      refine Ideal.span_le.2 ?_
      rintro a ⟨x, hx, z, hz, e⟩
      obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx z hz
      have : a = c := S.U.inj (e.symm.trans e')
      rw [this]
      exact hc
    rw [phDecD_apply, h2 b (Ideal.mem_sup_right hb), hm b (hi hb)]
    simp

private theorem UpperTheory.V.Pa.phDec_expand {F A : Type} [Field F] [AddCommGroup A] (T : Submodule F (A →+ F)) {e : ℕ}
    (v : Module.Basis (Fin e) F T) (d : T) (b : A) :
    (d : A →+ F) b = ∑ k, (v k : A →+ F) b * v.coord k d := by
  let ev : T →ₗ[F] F :=
    { toFun := fun α => (α : A →+ F) b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev d = ∑ k, ev (v k) * v.coord k d

  conv_lhs => rw [← v.sum_repr d, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, Module.Basis.coord_apply]

theorem UpperTheory.V.Pa.phDec :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Φ ∈ S.Ph, ∃ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) ∧ (∀ k, μ k ∈ S.La) ∧ ∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y := by
  intro l _ S Φ hΦ
  have : Module.Finite S.F S.Tp := (tpDual l S).1
  let v := Module.finBasis S.F S.Tp
  let D : S.U.N →+ S.Tp :=
    { toFun := fun y => ⟨phDecD S Φ y, phDecD_mem S Φ hΦ y⟩
      map_zero' := by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp [phDecD_apply]
      map_add' := fun y y' => by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp only [Submodule.coe_add, AddMonoidHom.add_apply, phDecD_apply, smul_add, map_add (f := _)]
        ring }
  have hD : ∀ y b, (D y : S.Bh →+ S.F) b = Φ (b • y) - S.rF b * Φ y := fun _ _ => rfl
  have hs : ∀ (c : S.Bh) y, D (c • y) = S.rF c • D y := by
    intro c y
    refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
    have := (D y).2.1 b c
    rw [hD, hD, hD, map_mul] at this
    rw [Submodule.coe_smul, AddMonoidHom.smul_apply, hD, hD, smul_smul, smul_eq_mul]
    linear_combination this
  refine ⟨_, fun k => v k, fun k => (v.coord k).toAddMonoidHom.comp D, fun k => (v k).2, fun k c y => ?_,
    fun b y => ?_⟩
  · change v.coord k (D (c • y)) = S.rF c * v.coord k (D y)
    rw [hs, map_smul, smul_eq_mul]
  · have := phDec_expand S.Tp v (D y) b
    rw [hD] at this
    change Φ (b • y) = S.rF b * Φ y + ∑ k, (v k : S.Bh →+ S.F) b * v.coord k (D y)
    rw [← this]
    ring
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.laInj :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ μ ∈ S.La, S.laC μ ∈ BdM S.h S.x S.F → μ = 0 := by
  intro l _ S μ hμ hB
  obtain ⟨Y, -, -, hY⟩ := hB
  obtain ⟨-, p2, p3, p4, -⟩ := prAdd l S
  have hμ' : ∀ (b : S.Bh) y, μ (b • y) = S.rF b * μ y := hμ
  have hinv : ∀ g, S.ρ S.F g⁻¹ * S.ρ S.F g = 1 := by
    intro g
    simp only [Ctx.ρ, NP.ρX, mat]
    rw [← Matrix.map_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : ∀ y : S.U.N, S.pr0 (y : S.U.AA) = 0 ∧ S.pr1 (y : S.U.AA) = y := by
    intro y
    simpa using p2 0 y
  have h0 : S.pr0 0 = 0 ∧ S.pr1 0 = 0 := hN 0
  have key : ∀ Z ∈ Submodule.span S.Bh (Set.range S.U.vr),
      Z.map (fun a => μ (S.pr1 a)) =
        Z.map (fun a => S.rF (S.pr0 a)) * Y - Y * Z.map (fun a => S.rF (S.pr0 a)) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, rfl⟩ := hZ
      have e0 : (S.U.vr g).map (fun a => S.rF (S.pr0 a)) = S.ρ S.F g := by
        ext i j; exact (prVr l S g i j).1
      have e1 : (S.U.vr g).map (fun a => μ (S.pr1 a)) * S.ρ S.F g⁻¹ =
          S.ρ S.F g * Y * S.ρ S.F g⁻¹ - Y := congrFun hY g
      have e2 := congrArg (· * S.ρ S.F g) e1
      simp only [Matrix.mul_assoc, Matrix.sub_mul, hinv, Matrix.mul_one] at e2
      rw [e0, e2]
    | zero =>
      have a0 : (0 : Matrix (Fin S.n) (Fin S.n) S.U.AA).map (fun a => S.rF (S.pr0 a)) = 0 := by
        ext i j; simp [h0.1]
      have a1 : (0 : Matrix (Fin S.n) (Fin S.n) S.U.AA).map (fun a => μ (S.pr1 a)) = 0 := by
        ext i j; simp [h0.2]
      rw [a0, a1]; simp
    | add Z Z' _ _ h h' =>
      have a0 : (Z + Z').map (fun a => S.rF (S.pr0 a)) =
          Z.map (fun a => S.rF (S.pr0 a)) + Z'.map (fun a => S.rF (S.pr0 a)) := by
        ext i j; simp [(p3 _ _).1]
      have a1 : (Z + Z').map (fun a => μ (S.pr1 a)) =
          Z.map (fun a => μ (S.pr1 a)) + Z'.map (fun a => μ (S.pr1 a)) := by
        ext i j; simp [(p3 _ _).2]
      rw [a0, a1, h, h', Matrix.add_mul, Matrix.mul_add]; abel
    | smul b Z _ h =>
      have a0 : (b • Z).map (fun a => S.rF (S.pr0 a)) = S.rF b • Z.map (fun a => S.rF (S.pr0 a)) := by
        ext i j; simp [(p4 _ _).1]
      have a1 : (b • Z).map (fun a => μ (S.pr1 a)) = S.rF b • Z.map (fun a => μ (S.pr1 a)) := by
        ext i j; simp [(p4 _ _).2, hμ']
      rw [a0, a1, h, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  ext y
  rcases S.x.a_le.eq_or_lt with ha | ha
  · have hy : y = 0 := by
      apply Subtype.ext
      exact (S.U.typeI ha).le y.2
    rw [hy, map_zero, map_zero]
  · have hp := S.x.a_pos
    let i : Fin S.n := ⟨0, by omega⟩
    let j : Fin S.n := ⟨S.x.a, ha⟩
    have hm : Matrix.single i j (y : S.U.AA) ∈ Submodule.span S.Bh (Set.range S.U.vr) := by
      rw [S.U.span]
      intro i' j'
      by_cases e : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := e
        refine ⟨fun e => ?_, fun _ => by simp⟩
        exact absurd (e.1 (by simp only [i]; omega)) (by simp [j])
      · rw [Matrix.single_apply_of_ne _ _ _ _ _ e]
        exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    have a0 : (Matrix.single i j (y : S.U.AA)).map (fun a => S.rF (S.pr0 a)) = 0 := by
      ext i' j'
      by_cases e : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := e
        simp [(hN y).1]
      · simp [Matrix.single_apply_of_ne _ _ _ _ _ e, h0.1]
    have k := key _ hm
    rw [a0] at k
    have k' := congrFun (congrFun k i) j
    simpa [(hN y).2] using k'
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A)
  (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
  (V : Submodule A (Matrix (Fin n) (Fin n) R))

end

private theorem C_smul_mem_w2 {n : ℕ} {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {e a : ℕ}
    (c : X) (M : Matrix (Fin n) (Fin n) (DD X e)) (hM : M ∈ W2 n A X e a) :
    (DD.C c : DD X e) • M ∈ W2 n A X e a := by
  simp only [W2, blkMat, ddPart, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hM ⊢
  intro i j
  obtain ⟨h1, h2⟩ := hM i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · obtain ⟨p, q, r, s⟩ := h1 hij
    refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
    · simp [Matrix.smul_apply, DD.mul_a, DD.C_a, p hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep, DD.C_ep, DD.C_a, q hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep', DD.C_ep', DD.C_a, r hf]
    · simp [Matrix.smul_apply, DD.mul_eta, DD.C_ep, DD.C_ep', DD.C_eta, DD.C_a, s hf]
  · obtain ⟨p, q, r, s⟩ := h2 hij
    refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
    · simp [Matrix.smul_apply, DD.mul_a, DD.C_a, p hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep, DD.C_ep, DD.C_a, q hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep', DD.C_ep', DD.C_a, r hf]
    · simp [Matrix.smul_apply, DD.mul_eta, DD.C_ep, DD.C_ep', DD.C_eta, DD.C_a, s hf]

private theorem smul_add_smul_mem_selZ {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Type} [CommRing A] (F : GFrame l)
    {R : Type} [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R))
    (d₁ d₂ : R) (hd₁ : ∀ M ∈ V, d₁ • M ∈ V) (hd₂ : ∀ M ∈ V, d₂ • M ∈ V)
    (z₁ z₂ : F.G₀ → Matrix (Fin n) (Fin n) R) (h₁ : z₁ ∈ SelZ F t ρ w wi V) (h₂ : z₂ ∈ SelZ F t ρ w wi V) :
    (fun g => d₁ • z₁ g + d₂ • z₂ g) ∈ SelZ F t ρ w wi V := by
  obtain ⟨a1, b1, c1, e1, f1, g1⟩ := h₁
  obtain ⟨a2, b2, c2, e2, f2, g2⟩ := h₂
  refine ⟨fun g => V.add_mem (hd₁ _ (a1 g)) (hd₂ _ (a2 g)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j N
    have k1 := (b1 i j N).comp (fun q => Ideal.Quotient.mk _ d₁ * q)
    have k2 := (b2 i j N).comp (fun q => Ideal.Quotient.mk _ d₂ * q)
    convert k1.add k2 using 1
    funext g
    simp [Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_mul]
  · intro g g'
    simp only [c1, c2, smul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add]
    abel
  · intro g
    simp only [e1, e2, Matrix.transpose_add, Matrix.transpose_smul, smul_neg, neg_add]
  · intro u g hg
    simp [f1 u g hg, f2 u g hg]
  · intro v
    obtain ⟨Y1, hY1, L1⟩ := g1 v
    obtain ⟨Y2, hY2, L2⟩ := g2 v
    refine ⟨d₁ • Y1 + d₂ • Y2, V.add_mem (hd₁ _ hY1) (hd₂ _ hY2), ?_⟩
    intro γ
    obtain ⟨p1, q1⟩ := L1 γ
    obtain ⟨p2, q2⟩ := L2 γ
    have key : wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v
        = d₁ • (wi v * (z₁ (F.φ v γ) - dY F ρ Y1 (F.φ v γ)) * w v)
          + d₂ • (wi v * (z₂ (F.φ v γ) - dY F ρ Y2 (F.φ v γ)) * w v) := by
      simp only [dY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_sub, smul_add]
      abel
    refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
    · show (wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v) i j = 0
      rw [key]
      simp [Matrix.add_apply, Matrix.smul_apply, p1 i j hij, p2 i j hij]
    · show (wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v) i i = 0
      rw [key]
      simp [Matrix.add_apply, Matrix.smul_apply, q1 hg i, q2 hg i]

private theorem zero_mem_selZ {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Type} [CommRing A] (F : GFrame l)
    {R : Type} [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) :
    (0 : F.G₀ → Matrix (Fin n) (Fin n) R) ∈ SelZ F t ρ w wi V := by
  refine ⟨fun g => V.zero_mem, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j N
    simp only [Pi.zero_apply, Matrix.zero_apply, map_zero]
    exact IsLocallyConstant.const 0
  · intro g g'
    simp
  · intro g
    simp
  · intro u g hg
    rfl
  · intro v
    refine ⟨0, V.zero_mem, fun γ => ⟨fun i j hij => ?_, fun hg i => ?_⟩⟩ <;> simp [dY]

private theorem bndF_mul_add_mul (K G : Type) [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (c₁ c₂ : FractionRing (PowerSeries K)) (φ ψ : G → FractionRing (PowerSeries K))
    (h1 : BndF (PowerSeries.X : PowerSeries K) φ) (h2 : BndF (PowerSeries.X : PowerSeries K) ψ) :
    BndF (PowerSeries.X : PowerSeries K) (fun g => c₁ * φ g + c₂ * ψ g) := by
  obtain ⟨hc, hop, -⟩ := bndOps K G
  exact (hop _ _ (hop _ _ (hc c₁) h1).2.1 (hop _ _ (hc c₂) h2).2.1).1

private theorem bndD_C_smul_add_C_smul {K G : Type} [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {n e : ℕ} (c₁ c₂ : FractionRing (PowerSeries K))
    (Ψ₁ Ψ₂ : G → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e))
    (h1 : BndD (PowerSeries.X : PowerSeries K) Ψ₁) (h2 : BndD (PowerSeries.X : PowerSeries K) Ψ₂) :
    BndD (PowerSeries.X : PowerSeries K)
      (fun g => (DD.C c₁ : DD (FractionRing (PowerSeries K)) e) • Ψ₁ g + (DD.C c₂ : DD _ e) • Ψ₂ g) := by
  intro i j
  obtain ⟨a1, b1, p1, e1⟩ := h1 i j
  obtain ⟨a2, b2, p2, e2⟩ := h2 i j
  refine ⟨?_, fun k => ?_, fun k => ?_, ?_⟩
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_a, DD.mul_a, DD.C_a] using
      bndF_mul_add_mul K G c₁ c₂ _ _ a1 a2
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_ep, DD.mul_ep, DD.C_a, DD.C_ep] using
      bndF_mul_add_mul K G c₁ c₂ _ _ (b1 k) (b2 k)
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_ep', DD.mul_ep', DD.C_a, DD.C_ep'] using
      bndF_mul_add_mul K G c₁ c₂ _ _ (p1 k) (p2 k)
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_eta, DD.mul_eta, DD.C_a, DD.C_ep, DD.C_ep',
      DD.C_eta] using bndF_mul_add_mul K G c₁ c₂ _ _ e1 e2

theorem UpperTheory.V.Pa.liftsSub :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), Lifts h k 0 ∧ (∀ z z' : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr, Lifts h k z → Lifts h k z' → Lifts h k (z + z')) ∧ ∀ (c : x.Fr) (z : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr), Lifts h k z → Lifts h k (c • z) := by
  intro l _ L G G0 h n x k
  have hV : ∀ (c : x.Fr), ∀ M ∈ W2 n x.A x.Fr k.g x.a, (DD.C c : DD x.Fr k.g) • M ∈ W2 n x.A x.Fr k.g x.a :=
    fun c M hM => C_smul_mem_w2 c M hM
  have lin : ∀ (c₁ c₂ : x.Fr) (z₁ z₂ : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr),
      Lifts h k z₁ → Lifts h k z₂ → Lifts h k (fun j γ => c₁ • z₁ j γ + c₂ • z₂ j γ) := by
    rintro c₁ c₂ z₁ z₂ ⟨Ψ₁, m1, b1, e1⟩ ⟨Ψ₂, m2, b2, e2⟩
    refine ⟨fun γ => (DD.C c₁ : DD x.Fr k.g) • Ψ₁ γ + (DD.C c₂ : DD x.Fr k.g) • Ψ₂ γ,
      smul_add_smul_mem_selZ _ _ _ _ _ _ _ _ (hV c₁) (hV c₂) _ _ m1 m2, bndD_C_smul_add_C_smul c₁ c₂ _ _ b1 b2, ?_⟩
    intro j γ a b
    simp [Matrix.add_apply, Matrix.smul_apply, DD.add_ep', DD.mul_ep', DD.C_a, DD.C_ep', e1 j γ a b, e2 j γ a b]
  refine ⟨?_, fun z z' hz hz' => ?_, fun c z hz => ?_⟩
  · refine ⟨0, zero_mem_selZ _ _ _ _ _ _, ?_, ?_⟩
    · intro i j
      obtain ⟨hc, -⟩ := bndOps x.K G.frame.G₀
      refine ⟨by simpa using hc 0, fun _ => by simpa using hc 0, fun _ => by simpa using hc 0, by simpa using hc 0⟩
    · intro j γ a b
      simp
  · convert lin 1 1 z z' hz hz' using 1
    funext j γ
    simp
  · convert lin c 0 z z hz hz using 1
    funext j γ
    simp
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem selLift {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R R' : Type} [CommRing A] [CommRing R] [CommRing R']
    [Algebra A R] [Algebra A R'] (t : A) (f : R →+* R') (hf : Function.Injective f)
    (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' : F.G₀ → Matrix (Fin n) (Fin n) R') (w' wi' : F.Vl → Matrix (Fin n) (Fin n) R')
    (hρ : ∀ g, (ρ g).map f = ρ' g) (hw : ∀ g, (w g).map f = w' g) (hwi : ∀ g, (wi g).map f = wi' g)
    (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R'))
    (c : R') (hV : ∀ Z : Matrix (Fin n) (Fin n) R, ∀ Z' ∈ V', Z.map f = c • Z' → Z ∈ V)
    (z' : F.G₀ → Matrix (Fin n) (Fin n) R') (hz' : z' ∈ SelZ F t ρ' w' wi' V')
    (Y' : F.Vl → Matrix (Fin n) (Fin n) R') (hY' : ∀ v, Y' v ∈ V' ∧ LocAt F ρ' w' wi' z' v (Y' v))
    (z : F.G₀ → Matrix (Fin n) (Fin n) R) (hc : ∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => z g i j)
    (hz : ∀ g, (z g).map f = c • z' g) (Y : F.Vl → Matrix (Fin n) (Fin n) R) (hY : ∀ v, (Y v).map f = c • Y' v) :
    z ∈ SelZ F t ρ w wi V := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hz'
  have inj : Function.Injective fun Z : Matrix (Fin n) (Fin n) R => Z.map f := Matrix.map_injective hf
  refine ⟨fun g => hV _ _ (h1 g) (hz g), hc, fun g g' => inj ?_, fun g => inj ?_, fun u g hg => inj ?_,
    fun v => ⟨Y v, hV _ _ (hY' v).1 (hY v), fun g => ?_⟩⟩
  · simp only [Matrix.map_add f (map_add f), Matrix.map_mul, hz, hρ, h3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
  · simp only [Matrix.map_neg f (map_neg f), Matrix.transpose_map, hz, h4, smul_neg, Matrix.transpose_smul]
  · simp only [hz, h5 u g hg, smul_zero, Matrix.map_zero f (map_zero f)]
  · have key : (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v).map f =
        c • (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) := by
      simp only [dY, Matrix.map_sub f (map_sub f), Matrix.map_mul, hz, hρ, hw, hwi, hY, ← smul_sub, Matrix.mul_smul,
        Matrix.smul_mul]
    have k2 : ∀ i j, (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) i j = 0 →
        (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v) i j = 0 := by
      intro i j h0
      apply hf
      have := congrFun (congrFun key i) j
      rw [Matrix.map_apply, Matrix.smul_apply, h0, smul_zero] at this
      rw [this, map_zero]
    exact ⟨fun i j hij => k2 i j (((hY' v).2 g).1 i j hij), fun hg i => k2 i i (((hY' v).2 g).2 hg i)⟩

private theorem liftF {K Γ : Type} [Field K] [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ] {n : ℕ}
    (z : Γ → Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K))) (hz : BndM (PowerSeries.X : PowerSeries K) z) :
    ∀ᶠ s : ℕ in Filter.atTop, ∃ z' : Γ → Matrix (Fin n) (Fin n) (PowerSeries K),
      (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) (PowerSeries K) PowerSeries.X}) fun g => z' g i j) ∧
      ∀ g, (z' g).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) =
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s) • z g := by
  have B := fun φ hφ => Filter.eventually_atTop.2 ((bndOps K Γ).2.2.2.2 φ hφ)
  have e1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j)
  filter_upwards [e1] with s a1
  choose b1 c1 a1 using a1
  refine ⟨fun g => Matrix.of fun i j => b1 i j g, fun i j => c1 i j, fun g => ?_⟩
  ext i j
  exact a1 i j g

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.selScale :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ b : Bool, ∀ z ∈ SelZ G.frame x.t (fun g => x.ρX x.Fr (h.p₀ g)) (x.wX x.Fr) (x.wiX x.Fr) (if b then Ev x.A x.Fr n x.a else Od x.A x.Fr n x.a), BndM x.t z → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ z' ∈ SelZ G.frame x.t (fun g => x.ρX x.A (h.p₀ g)) (x.wX x.A) (x.wiX x.A) (if b then Ev x.A x.A n x.a else Od x.A x.A n x.a), ∀ g, (z' g).map (algebraMap x.A x.Fr) = algebraMap x.A x.Fr x.t ^ s • z g := by
  intro l _ L G G0 h n x b z hz hb
  choose Y hY using hz.2.2.2.2.2
  have c0 := (bndOps x.K G.G₀).1
  have e1 := liftF z hb
  have e2 := Filter.eventually_all.2 fun v => liftF (K := x.K) (fun _ : G.G₀ => Y v) fun i j => c0 _
  apply Filter.eventually_atTop.1
  filter_upwards [e1, e2] with s a1 a2
  obtain ⟨z', hc, hz'⟩ := a1
  choose Y' _ hY' using a2
  have hf : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective _ _
  refine ⟨z', selLift G.frame x.t (algebraMap x.A x.Fr) hf _ _ _ _ _ _ (fun g => rfl) (fun v => rfl) (fun v => rfl)
    _ _ (algebraMap x.A x.Fr x.t ^ s) (fun Z Z' hZ' hZ => ?_) z hz Y hY z' hc hz' (fun v => Y' v 1) (fun v => hY' v 1), hz'⟩
  have key : ∀ i j, Z' i j = 0 → Z i j = 0 := fun i j e => hf (by
    have := congrFun (congrFun hZ i) j
    rw [Matrix.map_apply, Matrix.smul_apply, e, smul_zero] at this
    rw [this, map_zero])
  cases b
  · exact fun i j => ⟨fun e => key i j ((hZ' i j).1 e), fun _ => trivial⟩
  · exact fun i j => ⟨fun _ => trivial, fun e => key i j ((hZ' i j).2 e)⟩
end
