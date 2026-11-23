module

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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

private theorem dd_fin (X : Type) [CommRing X] (g : ℕ) : Module.Finite X (DD X g) := by
  let f : (X × (Fin g → X) × (Fin g → X) × X) →ₗ[X] DD X g :=
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      map_add' := fun p q => DD.ext (by simp) (by ext j; simp) (by ext j; simp) (by simp)
      map_smul' := fun c p => by
        have hC : (DD.C c : DD X g) = ⟨c, 0, 0, 0⟩ := rfl
        simp only [RingHom.id_apply]
        change _ = DD.C c * _
        rw [hC]
        apply DD.ext <;> (try funext j) <;> simp }
  refine Module.Finite.of_surjective f ?_
  intro y
  exact ⟨(y.a, y.ep, y.ep', y.eta), rfl⟩

private theorem dd_nil (X : Type) [CommRing X] (g : ℕ) : RingHom.ker (DD.aug X g) ^ 3 = ⊥ := by
  set I := RingHom.ker (DD.aug X g) with hIdef
  have hI : ∀ y ∈ I, y.a = 0 := fun y hy => RingHom.mem_ker.mp hy
  have h2 : ∀ w ∈ I ^ 2, w.a = 0 ∧ w.ep = 0 ∧ w.ep' = 0 := by
    intro w hw
    rw [sq] at hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · intro m hm n hn
      have e1 := hI m hm
      have e2 := hI n hn
      refine ⟨by simp [e1, e2], by ext j; simp [e1, e2], by ext j; simp [e1, e2]⟩
    · rintro x y ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩
      refine ⟨by simp [h1, h4], by ext j; simp [h2, h5], by ext j; simp [h3, h6]⟩
  rw [eq_bot_iff, pow_succ, Ideal.mul_le]
  intro r hr s hs
  obtain ⟨a1, a2, a3⟩ := h2 r hr
  have e := hI s hs
  rw [Ideal.mem_bot]
  apply DD.ext
  · simp [a1]
  · ext j
    simp [a1, a2, e]
  · ext j
    simp [a1, a3, e]
  · simp [a1, a2, a3, e]

theorem UpperTheory.V.Pa.testEx :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F) (Φ : S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) → (∀ k, μ k ∈ S.La) → (∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y) → ∃ θ : S.U.AA →+* DD S.F e, S.Test (DD S.F e) (DD.aug S.F e) θ ∧ ∀ a, θ a = ⟨S.rF (S.pr0 a), fun k => μ k (S.pr1 a), fun k => α k (S.pr0 a), Φ (S.pr1 a)⟩ := by
  intro l _ S e α μ Φ hα hμ hΦ
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := prAdd l S
  have hα' : ∀ k, (∀ b b', α k (b * b') = S.rF b * α k b' + S.rF b' * α k b) ∧
      (∀ o, α k (algebraMap S.OO S.Bh o) = 0) ∧ ∀ b ∈ ired S.U.N, α k b = 0 := fun k => hα k
  have hμ' : ∀ k (b : S.Bh) y, μ k (b • y) = S.rF b * μ k y := fun k => hμ k
  have q0 : ∀ b : S.Bh, S.pr0 (algebraMap S.Bh S.U.AA b) = b := fun b => by simpa using (p2 b 0).1
  have q1 : ∀ b : S.Bh, S.pr1 (algebraMap S.Bh S.U.AA b) = 0 := fun b => by simpa using (p2 b 0).2
  have o0 : S.pr0 1 = 1 := by simpa using q0 1
  have o1 : S.pr1 1 = 0 := by simpa using q1 1
  have z0 : S.pr0 0 = 0 := by simpa using q0 0
  have z1 : S.pr1 0 = 0 := by simpa using q1 0
  have hα1 : ∀ k, α k 1 = 0 := fun k => by simpa using (hα' k).2.1 1
  let T : S.U.AA → DD S.F e := fun a =>
    ⟨S.rF (S.pr0 a), fun k => μ k (S.pr1 a), fun k => α k (S.pr0 a), Φ (S.pr1 a)⟩
  have hmul : ∀ a a', T (a * a') = T a * T a' := by
    intro a a'
    have hd : S.rF (S.pr0 (a * a')) = S.rF (S.pr0 a) * S.rF (S.pr0 a') := by
      have h0 : S.pr0 (a * a') - S.pr0 a * S.pr0 a' ∈ RingHom.ker S.rF := by
        rw [S.rF_ker]
        exact p6 (p5 a a').1
      rw [RingHom.mem_ker, map_sub, map_mul, sub_eq_zero] at h0
      exact h0
    have hda : ∀ k, α k (S.pr0 (a * a')) =
        S.rF (S.pr0 a) * α k (S.pr0 a') + S.rF (S.pr0 a') * α k (S.pr0 a) := by
      intro k
      have h0 := (hα' k).2.2 _ (p5 a a').1
      rw [map_sub, sub_eq_zero] at h0
      rw [h0, (hα' k).1]
    have hp1 := (p5 a a').2
    apply DD.ext
    · simp only [T, DD.mul_a]
      exact hd
    · funext k
      simp only [T, DD.mul_ep]
      rw [hp1, map_add (f := _), hμ', hμ']
      ring
    · funext k
      simp only [T, DD.mul_ep']
      rw [hda k]
      ring
    · simp only [T, DD.mul_eta]
      rw [hp1, map_add (f := _), hΦ, hΦ, Finset.sum_add_distrib]
      have s1 : ∑ j, μ j (S.pr1 a) * α j (S.pr0 a') = ∑ j, α j (S.pr0 a') * μ j (S.pr1 a) :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [s1]
      ring
  let θ : S.U.AA →+* DD S.F e :=
    { toFun := T
      map_one' := DD.ext (by simp [T, o0]) (by funext k; simp [T, o1]) (by funext k; simp [T, o0, hα1])
        (by simp [T, o1])
      map_mul' := hmul
      map_zero' := DD.ext (by simp [T, z0]) (by funext k; simp [T, z1]) (by funext k; simp [T, z0])
        (by simp [T, z1])
      map_add' := fun a a' => DD.ext (by simp [T, (p3 a a').1]) (by funext k; simp [T, (p3 a a').2])
        (by funext k; simp [T, (p3 a a').1]) (by simp [T, (p3 a a').2]) }
  have hAlg : ∀ c : S.F, algebraMap S.F (DD S.F e) c = ⟨c, 0, 0, 0⟩ := fun c => rfl
  refine ⟨θ, ⟨dd_fin _ _, ⟨3, dd_nil _ _⟩, fun a => rfl, fun o => ?_⟩, fun a => rfl⟩
  rw [hAlg]
  apply DD.ext
  · simp [θ, T, q0]
  · funext k
    simp [θ, T, q1]
  · funext k
    simp [θ, T, q0, (hα' k).2.1]
  · simp [θ, T, q1]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem adicDD {A Γ : Type} [CommRing A] [TopologicalSpace Γ] {e : ℕ} (t : A) (d : Γ → DD A e)
    (h1 : AdicCont (Ideal.span {t}) fun g => (d g).a)
    (h2 : ∀ k, AdicCont (Ideal.span {t}) fun g => (d g).ep k)
    (h3 : ∀ k, AdicCont (Ideal.span {t}) fun g => (d g).ep' k)
    (h4 : AdicCont (Ideal.span {t}) fun g => (d g).eta) :
    AdicCont (Ideal.span {algebraMap A (DD A e) t}) d := by
  intro N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have e1 := (h1 N).eventually_eq x
  have e2 := Filter.eventually_all.2 fun k => (h2 k N).eventually_eq x
  have e3 := Filter.eventually_all.2 fun k => (h3 k N).eventually_eq x
  have e4 := (h4 N).eventually_eq x
  filter_upwards [e1, e2, e3, e4] with y a1 a2 a3 a4
  simp only [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at a1 a2 a3 a4 ⊢
  obtain ⟨b1, a1⟩ := a1
  obtain ⟨b4, a4⟩ := a4
  choose b2 a2 using a2
  choose b3 a3 using a3
  refine ⟨⟨b1, b2, b3, b4⟩, ?_⟩
  rw [← map_pow]
  have : algebraMap A (DD A e) (t ^ N) = DD.C (t ^ N) := rfl
  rw [this, sub_eq_add_neg]
  ext <;> simp [-map_pow, a1, a2, a3, a4, sub_eq_add_neg]

private theorem mapInj {X Y : Type} [CommRing X] [CommRing Y] {e : ℕ} (f : X →+* Y) (hf : Function.Injective f) :
    Function.Injective (DD.map (g := e) f) := by
  intro u v h
  have h1 := congrArg DD.a h
  have h2 := congrArg DD.ep h
  have h3 := congrArg DD.ep' h
  have h4 := congrArg DD.eta h
  ext k
  · exact hf h1
  · exact hf (congrFun h2 k)
  · exact hf (congrFun h3 k)
  · exact hf h4

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

private theorem liftM {K Γ : Type} [Field K] [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ] {n e : ℕ}
    (z : Γ → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e)) (hz : BndD (PowerSeries.X : PowerSeries K) z) :
    ∀ᶠ s : ℕ in Filter.atTop, ∃ z' : Γ → Matrix (Fin n) (Fin n) (DD (PowerSeries K) e),
      (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) (DD (PowerSeries K) e) PowerSeries.X}) fun g => z' g i j) ∧
      ∀ g, (z' g).map (DD.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) =
        (DD.C (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s) : DD (FractionRing (PowerSeries K)) e) • z g := by
  have B := fun φ hφ => Filter.eventually_atTop.2 ((bndOps K Γ).2.2.2.2 φ hφ)
  have e1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j).1
  have e2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun k => B _ ((hz i j).2.1 k)
  have e3 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun k => B _ ((hz i j).2.2.1 k)
  have e4 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j).2.2.2
  filter_upwards [e1, e2, e3, e4] with s a1 a2 a3 a4
  choose b1 c1 a1 using a1
  choose b2 c2 a2 using a2
  choose b3 c3 a3 using a3
  choose b4 c4 a4 using a4
  refine ⟨fun g => Matrix.of fun i j => ⟨b1 i j g, fun k => b2 i j k g, fun k => b3 i j k g, b4 i j g⟩,
    fun i j => adicDD _ _ (c1 i j) (c2 i j) (c3 i j) (c4 i j), fun g => ?_⟩
  ext i j <;> simp [-map_pow, DD.map, a1, a2, a3, a4]

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.selScale1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ Sel1 h x.Fr k, BndD x.t z → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ z' ∈ Sel1 h x.A k, ∀ g, (z' g).map (DD.map (algebraMap x.A x.Fr)) = algebraMap x.A x.Fr x.t ^ s • z g := by
  intro l _ L G G0 h n x k z hz hb
  choose Y hY using hz.2.2.2.2.2
  have c0 := (bndOps x.K G.G₀).1
  have e1 := liftM z hb
  have e2 := Filter.eventually_all.2 fun v => liftM (K := x.K) (fun _ : G.G₀ => Y v)
    fun i j => ⟨c0 _, fun _ => c0 _, fun _ => c0 _, c0 _⟩
  apply Filter.eventually_atTop.1
  filter_upwards [e1, e2] with s a1 a2
  obtain ⟨z', hc, hz'⟩ := a1
  choose Y' _ hY' using a2
  have hf : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective _ _
  have m1 : ∀ M : Matrix (Fin n) (Fin n) x.A, (M.map (algebraMap x.A (DD x.A k.g))).map (DD.map (algebraMap x.A x.Fr)) =
      M.map (algebraMap x.A (DD x.Fr k.g)) := by
    intro M
    ext i j <;> first | rfl | exact map_zero (algebraMap x.A x.Fr)
  have m2 : ∀ Z : Fin k.g → Matrix (Fin n) (Fin n) x.A,
      (DD.epM fun j => (Z j).map (algebraMap x.A x.A)).map (DD.map (algebraMap x.A x.Fr)) =
      DD.epM fun j => (Z j).map (algebraMap x.A x.Fr) := by
    intro Z
    ext i j <;> first | rfl | exact map_zero (algebraMap x.A x.Fr)
  have m0 : (1 : Matrix (Fin n) (Fin n) (DD x.A k.g)).map (DD.map (algebraMap x.A x.Fr)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have p : ∀ (b1 b2 b3 b4 : Bool) (u : DD x.A k.g), ∀ u' ∈ ddPart x.A x.Fr k.g b1 b2 b3 b4,
      DD.map (algebraMap x.A x.Fr) u = DD.C (algebraMap x.A x.Fr x.t ^ s) * u' → u ∈ ddPart x.A x.A k.g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 u u' ⟨q1, q2, q3, q4⟩ hu
    refine ⟨fun e => hf ?_, fun e => funext fun j => hf ?_, fun e => funext fun j => hf ?_, fun e => hf ?_⟩
    · simpa [-map_pow, DD.map, q1 e] using congrArg DD.a hu
    · simpa [-map_pow, DD.map, q2 e] using congrFun (congrArg DD.ep hu) j
    · simpa [-map_pow, DD.map, q3 e] using congrFun (congrArg DD.ep' hu) j
    · simpa [-map_pow, DD.map, q4 e] using congrArg DD.eta hu
  refine ⟨z', selLift G.frame x.t (DD.map (algebraMap x.A x.Fr)) (mapInj _ hf) _ _ _ _ _ _ (fun g => ?_) (fun v => ?_) (fun v => ?_)
    _ _ (DD.C (algebraMap x.A x.Fr x.t ^ s)) (fun Z Z' hZ' hZ i j => ?_) z hz Y hY z' hc hz' (fun v => Y' v 1) (fun v => hY' v 1), hz'⟩
  · simp only [Kap.ρ1, NP.ρX, Matrix.map_mul, Matrix.map_add _ (map_add (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · simp only [Kap.w1, NP.wX, Matrix.map_mul, Matrix.map_sub _ (map_sub (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · simp only [Kap.wi1, NP.wiX, Matrix.map_mul, Matrix.map_add _ (map_add (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · have := congrFun (congrFun hZ i) j
    exact ⟨fun e => p _ _ _ _ _ _ ((hZ' i j).1 e) this, fun e => p _ _ _ _ _ _ ((hZ' i j).2 e) this⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa.SelmerFractionFieldBaseChange

variable {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (F : Type) [CommRing F] [Algebra x.A F]

end UpperTheory.V.Pa.SelmerFractionFieldBaseChange

private theorem selMap2_lemma {R S Γ : Type} [CommRing R] [CommRing S] [TopologicalSpace Γ] (I : Ideal R) (J : Ideal S)
    (π : R →+ S) (hπ : ∀ N u, u ∈ I ^ N → π u ∈ J ^ N) (f : Γ → R) (hf : AdicCont I f) :
    AdicCont J (fun g => π (f g)) := by
  intro N
  have hs := Ideal.Quotient.mk_surjective (I := I ^ N)
  have e : (fun g => Ideal.Quotient.mk (J ^ N) (π (f g))) =
      (fun q => Ideal.Quotient.mk (J ^ N) (π (Function.surjInv hs q))) ∘
        (fun g => Ideal.Quotient.mk (I ^ N) (f g)) := by
    funext g
    simp only [Function.comp]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hπ
    rw [← Ideal.Quotient.eq]
    exact (Function.surjInv_eq hs _).symm
  rw [e]
  exact (hf N).comp _

private theorem dd_components_mem_span_pow_of_mem_span_algebraMap_pow {A : Type} [CommRing A] (g : ℕ) (t : A) (N : ℕ) (u : DD A g)
    (hu : u ∈ Ideal.span {algebraMap A (DD A g) t} ^ N) :
    u.a ∈ Ideal.span {t} ^ N ∧ (∀ j, u.ep j ∈ Ideal.span {t} ^ N) ∧ (∀ j, u.ep' j ∈ Ideal.span {t} ^ N) ∧
      u.eta ∈ Ideal.span {t} ^ N := by
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.mem_span_singleton'] at hu
  obtain ⟨r, rfl⟩ := hu
  rw [Ideal.span_singleton_pow]
  have ha : (algebraMap A (DD A g) (t ^ N)).a = t ^ N := rfl
  have he : (algebraMap A (DD A g) (t ^ N)).ep = 0 := rfl
  have he' : (algebraMap A (DD A g) (t ^ N)).ep' = 0 := rfl
  have hη : (algebraMap A (DD A g) (t ^ N)).eta = 0 := rfl
  refine ⟨?_, fun j => ?_, fun j => ?_, ?_⟩
  · rw [DD.mul_a, ha]
    exact Ideal.mem_span_singleton'.mpr ⟨r.a, rfl⟩
  · rw [DD.mul_ep, ha, he]
    exact Ideal.mem_span_singleton'.mpr ⟨r.ep j, by simp⟩
  · rw [DD.mul_ep', ha, he']
    exact Ideal.mem_span_singleton'.mpr ⟨r.ep' j, by simp⟩
  · rw [DD.mul_eta, ha, he, he', hη]
    exact Ideal.mem_span_singleton'.mpr ⟨r.eta, by simp⟩

private theorem dd_map_algebraMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (c : A) :
    DD.map (algebraMap A B) (algebraMap A (DD A g) c) = algebraMap A (DD B g) c :=
  DD.ext rfl (funext fun _ => map_zero _) (funext fun _ => map_zero _) (map_zero _)

private theorem dd_map_mem_span_algebraMap_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (t : A) (N : ℕ) (u : DD A g)
    (hu : u ∈ Ideal.span {algebraMap A (DD A g) t} ^ N) :
    DD.map (algebraMap A B) u ∈ Ideal.span {algebraMap A (DD B g) t} ^ N := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu ⊢
  obtain ⟨r, rfl⟩ := hu
  exact ⟨DD.map (algebraMap A B) r, by rw [map_mul, map_pow, dd_map_algebraMap_algebraMap]⟩

private theorem ddMap_algebraMap_mem_ddPart {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (b1 b2 b3 b4 : Bool)
    (u : DD A g) (hu : u ∈ ddPart A A g b1 b2 b3 b4) : DD.map (algebraMap A B) u ∈ ddPart A B g b1 b2 b3 b4 := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · show algebraMap A B u.a = 0
    rw [h1 h, map_zero]
  · show (fun j => algebraMap A B (u.ep j)) = 0
    rw [h2 h]
    funext j
    exact map_zero _
  · show (fun j => algebraMap A B (u.ep' j)) = 0
    rw [h3 h]
    funext j
    exact map_zero _
  · show algebraMap A B u.eta = 0
    rw [h4 h, map_zero]

private theorem map_ddMap_algebraMap_mem_W2 {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g a : ℕ)
    (Z : Matrix (Fin n) (Fin n) (DD A g)) (hZ : Z ∈ W2 n A A g a) :
    Z.map (DD.map (algebraMap A B)) ∈ W2 n A B g a := by
  intro i j
  exact ⟨fun hc => ddMap_algebraMap_mem_ddPart g _ _ _ _ _ ((hZ i j).1 hc), fun hc => ddMap_algebraMap_mem_ddPart g _ _ _ _ _ ((hZ i j).2 hc)⟩

private theorem map_algebraMap_map_ddMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g : ℕ)
    (M : Matrix (Fin n) (Fin n) A) :
    (M.map (algebraMap A (DD A g))).map (DD.map (algebraMap A B)) = M.map (algebraMap A (DD B g)) := by
  exact Matrix.ext fun i j => dd_map_algebraMap_algebraMap (A := A) (B := B) g (M i j)

private theorem epM_map_ddMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g : ℕ)
    (Z : Fin g → Matrix (Fin n) (Fin n) A) :
    (DD.epM Z).map (DD.map (algebraMap A B)) = DD.epM (fun j => (Z j).map (algebraMap A B)) := by
  refine Matrix.ext fun i j => DD.ext ?_ ?_ ?_ ?_
  · exact map_zero (algebraMap A B)
  · rfl
  · funext m
    exact map_zero (algebraMap A B)
  · exact map_zero (algebraMap A B)

private theorem kap_rho1_map_ddMap_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (g : Fm.G₀) :
    (k.ρ1 x.A g).map (DD.map (algebraMap x.A B)) = k.ρ1 B g := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.ρ1 NP.ρX
  rw [e, map_mul, map_add (f := _), map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem w1_map_dd_map_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (v : Fm.Vl) :
    (k.w1 x.A v).map (DD.map (algebraMap x.A B)) = k.w1 B v := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.w1 NP.wX
  rw [e, map_mul, map_sub, map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem wi1_map_dd_map_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (v : Fm.Vl) :
    (k.wi1 x.A v).map (DD.map (algebraMap x.A B)) = k.wi1 B v := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.wi1 NP.wiX
  rw [e, map_mul, map_add (f := _), map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem selMap2_lemma_12 {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) {R S : Type} [CommRing R] [CommRing S]
    (Φ : R →+* S) (ρ z : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' z' : F.G₀ → Matrix (Fin n) (Fin n) S) (w' wi' : F.Vl → Matrix (Fin n) (Fin n) S)
    (hρ : ∀ g, ρ' g = (ρ g).map Φ) (hz : ∀ g, z' g = (z g).map Φ) (hw : ∀ v, w' v = (w v).map Φ)
    (hwi : ∀ v, wi' v = (wi v).map Φ) (v : F.Vl) (Y : Matrix (Fin n) (Fin n) R)
    (hL : LocAt F ρ w wi z v Y) : LocAt F ρ' w' wi' z' v (Y.map Φ) := by
  have eM : ∀ M : Matrix (Fin n) (Fin n) R, M.map Φ = Φ.mapMatrix M := fun _ => rfl
  intro g
  obtain ⟨h1, h2⟩ := hL g
  have e : wi' v * (z' (F.φ v g) - dY F ρ' (Y.map Φ) (F.φ v g)) * w' v =
      (wi v * (z (F.φ v g) - dY F ρ Y (F.φ v g)) * w v).map Φ := by
    simp only [dY, hρ, hz, hw, hwi, eM, map_mul, map_sub]
  refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
  · rw [e, Matrix.map_apply, h1 i j hij, map_zero]
  · rw [e, Matrix.map_apply, h2 hg i, map_zero]

open UpperTheory.V.Pa.SelmerFractionFieldBaseChange in
theorem UpperTheory.V.Pa.selMap2 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ Sel2 h x.A k, (fun g => (z g).map (DD.map (algebraMap x.A x.Fr))) ∈ Sel2 h x.Fr k ∧ BndD x.t fun g => (z g).map (DD.map (algebraMap x.A x.Fr)) := by
  intro l _ L G G0 h n x k z hz
  obtain ⟨hV, hC, hco, hcj, hIu, hloc⟩ := hz
  have eM : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A x.Fr)) = (DD.map (algebraMap x.A x.Fr)).mapMatrix M := fun _ => rfl
  refine ⟨⟨fun g => map_ddMap_algebraMap_mem_W2 n k.g x.a _ (hV g), fun i j => ?_, fun g1 g2 => ?_, fun g => ?_,
    fun u g hg => ?_, fun v => ?_⟩, fun i j => ⟨?_, fun m => ?_, fun m => ?_, ?_⟩⟩
  · exact selMap2_lemma _ _ (DD.map (algebraMap x.A x.Fr)).toAddMonoidHom
      (fun N u hu => dd_map_mem_span_algebraMap_pow k.g x.t N u hu) (fun g => z g i j) (hC i j)
  · beta_reduce
    beta_reduce at hco
    rw [hco g1 g2, ← kap_rho1_map_ddMap_algebraMap k x.Fr, ← kap_rho1_map_ddMap_algebraMap k x.Fr]
    simp only [eM, map_add (f := _), map_mul]
  · beta_reduce
    rw [hcj g]
    exact Matrix.ext fun i j => map_neg (DD.map (algebraMap x.A x.Fr)) (z g j i)
  · beta_reduce
    rw [hIu u g hg]
    exact Matrix.map_zero _ (map_zero _)
  · obtain ⟨Y, hY, hL⟩ := hloc v
    exact ⟨Y.map (DD.map (algebraMap x.A x.Fr)), map_ddMap_algebraMap_mem_W2 n k.g x.a _ hY,
      selMap2_lemma_12 G.frame (DD.map (algebraMap x.A x.Fr)) _ z _ _ _ _ _ _
        (fun g => (kap_rho1_map_ddMap_algebraMap k x.Fr _).symm) (fun g => rfl) (fun v => (w1_map_dd_map_algebraMap k x.Fr v).symm)
        (fun v => (wi1_map_dd_map_algebraMap k x.Fr v).symm) v Y hL⟩
  · refine ⟨0, fun g => (z g i j).a, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.a, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).1) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).ep m, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.ep m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.1 m) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).ep' m, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.ep' m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.2.1 m) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).eta, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.eta, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.2.2) (fun g => z g i j) (hC i j)
end
