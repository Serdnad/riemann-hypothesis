module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle034
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigLat

theorem mem_eigSp_iff' {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {x : W} : x ∈ eigSp ρ τ ↔ ∀ a, ρ a x = τ a • x := by
  simp [eigSp, sub_eq_zero]

theorem sum_smul_of_eig {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {n : ℕ} (a c : Fin n → O) {x : W}
    (hx : ∀ b, ρ b x = τ b • x) :
    ∑ m, τ (c m) • ρ (a m) x = τ (∑ m, c m * a m) • x := by

  simp only [hx, smul_smul, map_sum, map_mul, Finset.sum_smul]

theorem span_inf_eigSp : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ R R' L hj hρ hiR hL hσ hd
  obtain ⟨n, a, c, hsum, heq⟩ := ScaledCasimir.exists_scaledCasimir F
  have hd0 : ((NumberField.discr F : ℤ) : Ω) ≠ 0 := Int.cast_ne_zero.2 (NumberField.discr_ne_zero F)
  have hσd : σ (∑ m, c m * a m) = ((NumberField.discr F : ℤ) : Ω) := by rw [hsum, map_intCast]
  have hiσd : (i.comp σ) (∑ m, c m * a m) = i ((NumberField.discr F : ℤ) : Ω) := by
    rw [RingHom.comp_apply, hσd]
  have hid0 : i ((NumberField.discr F : ℤ) : Ω) ≠ 0 := (map_ne_zero i).2 hd0

  let P : V → V := fun v => ((NumberField.discr F : ℤ) : Ω)⁻¹ • ∑ m, σ (c m) • ρ (a m) v

  let P' : Module.End Ω' V' := (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m)
  have hP'apply : ∀ x, P' x = (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m) x := by
    intro x
    simp [P', LinearMap.sum_apply]
  have hPeig : ∀ v, P v ∈ eigSp ρ σ := by
    intro v
    refine mem_eigSp_iff'.2 fun b => ?_
    simp only [P]
    rw [map_smul, heq Ω V ρ σ b v, smul_comm]
  have hPL : ∀ v ∈ L, P v ∈ L := by
    intro v hv
    have h1 : (∑ m, σ (c m) • ρ (a m) v) ∈ L := by
      refine Submodule.sum_mem _ fun m _ => ?_
      exact L.smul_mem ⟨σ (c m), hσ _⟩ (hL _ _ hv)
    exact L.smul_mem ⟨_, hd⟩ h1
  have hjP : ∀ v, P' (j v) = j (P v) := by
    intro v
    rw [hP'apply]
    simp only [P]

    rw [hj.1, map_inv₀, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hj.1, hρ, RingHom.comp_apply]
  have hP'id : ∀ x ∈ eigSp ρ' (i.comp σ), P' x = x := by
    intro x hx
    rw [hP'apply, sum_smul_of_eig a c (mem_eigSp_iff'.1 hx), hiσd, smul_smul,
      inv_mul_cancel₀ hid0, one_smul]
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx2' : x ∈ eigSp ρ' (i.comp σ) := hx2
    have key : ∀ y ∈ Submodule.span R' (j '' (L : Set V)), P' y ∈ Submodule.span R'
        (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨e, he, rfl⟩ := hy
        rw [hjP]
        exact Submodule.subset_span ⟨P e, Submodule.mem_inf.2 ⟨hPL e he, hPeig e⟩, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        have h1 : P' (r • y) = r • P' y := by
          rw [Subring.smul_def, Subring.smul_def, map_smul]
        rw [h1]
        exact Submodule.smul_mem _ r hy
    have h2 := key x hx1
    rwa [hP'id x hx2'] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨he1, he2⟩ := Submodule.mem_inf.1 he
    have he2' : e ∈ eigSp ρ σ := he2
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨e, he1, rfl⟩, ?_⟩
    show j e ∈ eigSp ρ' (i.comp σ)
    refine mem_eigSp_iff'.2 fun b => ?_
    rw [hρ, mem_eigSp_iff'.1 he2', hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigLat
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem nonempty_pModel_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v) →
    Nonempty (PModel o x) := by
  intro o _ Ω _ _ κ _ x ⟨c, hc, h⟩
  have h' : ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => x j / x c),
      ∃ k ∈ Algebra.adjoin o (Set.range fun j => x j / x c), k ≠ 0 ∧ a = g / k := by
    intro a
    obtain ⟨u, hu, v, hv, rfl⟩ := h a
    by_cases hv0 : v = 0
    · exact ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [hv0]⟩
    · exact ⟨u, hu, v, hv, hv0, rfl⟩
  obtain ⟨X, ξ, s, tie, all, -, -, hover⟩ := GlobalTheory.T.exists_proper_integral_model Ω o κ x c hc h'
  exact ⟨{ X := X, ξ := ξ, s := s, hover := hover, all := all, tie := tie }⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange

theorem phiNormSq_baseChange : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (lab : Ψ → Ψ ⊕ Ψ) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : Ψ → Fin k → A.Λ) (bL : Ψ → Fin m → V) (T : Ψ → Matrix (Fin m) (Fin m) L), IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ (e : L →+* ℂ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) → Function.Injective j → ∀ (ρ' : 𝓞 E →+* Module.End ℂ V'), (∀ a x, ρ' a (j x) = j (A.ρ a x)) → (∀ τ a, eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a)) = j (eigComp A.ρ (A.σ (lab τ)) (v a))) → ∀ hb : V' → V' → ℂ, (∀ τ c c', hb (j (q τ c)) (j (q τ c')) = (A.Bq.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c)) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c'))) → PhiNormSq ρ' hb (A.I.map j) (4 * Real.pi)⁻¹ (fun τ => e.comp (A.σ (lab τ))) (fun τ i => j (bL τ i)) ((((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2) := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A lab r k m h v q bL T hv hq hfam hT e V' _ _ j hjs hji ρ' hρ' heig hb hhb
  classical
  obtain ⟨hvI, hvind, hvrel⟩ := hv
  have hsum : ∀ a : Fin r → 𝓞 E, ∑ i, ρ' (a i) (j (v i)) = j (∑ i, A.ρ (a i) (v i)) := by
    intro a

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hρ' _ _
  have hspan : oSpan ρ' (fun i => j (v i)) = (oSpan A.ρ v).map j := by
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.oSpan
    rw [AddMonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨a, i, rfl⟩
      exact ⟨A.ρ a (v i), ⟨a, i, rfl⟩, (hρ' a (v i)).symm⟩
    · rintro ⟨y, ⟨a, i, rfl⟩, rfl⟩
      exact ⟨a, i, (hρ' a (v i)).symm⟩
  have hrel : (oSpan ρ' (fun i => j (v i))).relIndex (A.I.map j) = (oSpan A.ρ v).relIndex A.I := by
    rw [hspan]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hji
  have hOF : IsOFamily ρ' (A.I.map j) (fun i => j (v i)) := by
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.IsOFamily
    refine ⟨fun i => AddSubgroup.mem_map_of_mem j (hvI i), fun a ha => hvind a (hji ?_), ?_⟩
    · rw [map_zero, ← hsum a]
      exact ha
    · rw [hrel]
      exact hvrel
  have hqe : ∀ τ c, j (q τ c) ∈ eigSp ρ' (e.comp (A.σ (lab τ))) := by
    intro τ c
    have hx0 := (hq τ).2 c
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.eig at hx0
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem] at hx0
    have hx := hx0.2
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    intro a
    rw [hρ', RingHom.comp_apply, ← hjs, ← map_sub, hx a, map_zero]
  have happ : ∀ τ i, Fin.append (fun a => eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a))) (fun c => j (q τ c)) i =
      ∑ j', (T τ).map e j' (Fin.cast h i) • j (bL τ j') := by
    intro τ i
    have hfi := hfam τ i
    have hap : Fin.append (fun a => eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a))) (fun c => j (q τ c)) i =
        j (A.fam (lab τ) v (q τ) i) := by
      unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.fam
      refine Fin.addCases (fun a => ?_) (fun c => ?_) i
      · simp only [Fin.append_left, heig]
      · simp only [Fin.append_right]

    rw [hap, hfi, map_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hjs, Matrix.map_apply]
  have hdet : ∀ τ, ((T τ).map e).det = e (T τ).det := by
    intro τ
    rw [RingHom.map_det]
    rfl
  have hg : ∀ τ, (Matrix.of fun c c' => hb (j (q τ c)) (j (q τ c'))).det.re = A.gramDet e (q τ) := by
    intro τ
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.gramDet
    congr 2
    ext c c'
    exact hhb τ c c'
  unfold GlobalTheory.CompanionTheory.Ar.Cusp.PhiNormSq
  refine ⟨r, k, h, fun i => j (v i), fun τ c => j (q τ c), fun τ => (T τ).map e, hOF, hqe, happ, ?_, ?_⟩
  · intro τ
    rw [hdet τ]
    exact (map_ne_zero e).mpr (hT τ)
  · rw [hrel]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hdet τ, hg τ]

end GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory

def locSub {F : Type} [Field F] (R : Subring F) (a : F) : Subring F :=
  Subring.closure ((R : Set F) ∪ {a⁻¹})

theorem le_locSub {F : Type} [Field F] (R : Subring F) (a : F) : R ≤ locSub R a :=
  fun _ h => Subring.subset_closure (Or.inl h)

theorem inv_mem_locSub {F : Type} [Field F] (R : Subring F) (a : F) : a⁻¹ ∈ locSub R a :=
  Subring.subset_closure (Or.inr rfl)

theorem mem_locSub_iff {F : Type} [Field F] {R : Subring F} {a : F} (ha : a ∈ R) (h0 : a ≠ 0) (b : F) :
    b ∈ locSub R a ↔ ∃ k : ℕ, a ^ k * b ∈ R := by
  constructor
  · intro hb
    induction hb using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨0, by simpa using hx⟩
      · rw [Set.mem_singleton_iff.1 hx]
        exact ⟨1, by simpa [h0] using R.one_mem⟩
    | zero => exact ⟨0, by simp⟩
    | one => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x + y) = a ^ l * (a ^ k * x) + a ^ k * (a ^ l * y) := by ring
      rw [e]
      exact R.add_mem (R.mul_mem (R.pow_mem ha _) hk) (R.mul_mem (R.pow_mem ha _) hl)
    | neg x _ hx =>
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by simpa using R.neg_mem hk⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x * y) = (a ^ k * x) * (a ^ l * y) := by ring
      rw [e]
      exact R.mul_mem hk hl
  · rintro ⟨k, hk⟩
    have e : b = (a⁻¹) ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.one_mul]
    rw [e]
    exact (locSub R a).mul_mem ((locSub R a).pow_mem (inv_mem_locSub R a) _) (le_locSub R a hk)

structure IsPiece {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens)
    (R : Subring Ω) : Prop where
  affine : IsAffineOpen U
  spec : ∀ q : X, q ∈ U → genPt ξ ⤳ q
  ring : ∀ a : Ω, a ∈ R ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q

def stepMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : F :=
  (A.submatrix J (Fin.castLE i.2)).det

variable {Ω : Type} [Field Ω] {S : Type} {r n : S → ℕ}

def flagB (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  (M s * T s).map (algebraMap Ω (GenField Ω r)) * genU Ω r s

def ratioRing (R : Subring Ω) (B : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) : Subring (GenField Ω r) :=
  Subring.closure (((R.map (algebraMap Ω (GenField Ω r)) : Subring _) : Set (GenField Ω r)) ∪
    {a | ∃ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      a = stepMinor (B q.1) q.2 J' / stepMinor (B q.1) q.2 (J q)})

def chartSub {F : Type} [Field F] {κ : Type} (x : κ → F) (c : κ) : Subring F :=
  (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).toSubring

theorem stepMinor_smul {F : Type} [CommRing F] {n r : ℕ} (b : F) (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : stepMinor (b • A) i J = b ^ ((i : ℕ) + 1) * stepMinor A i J := by
  unfold stepMinor
  rw [Matrix.submatrix_smul]
  simp [Matrix.det_smul]

theorem flagMat_eq {E : Type} [AddCommGroup E] [Module Ω E] {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (s : S) :
    flagMat φ cc s = (algebraMap Ω (GenField Ω r) a ^ m s) • flagB M T s := by
  unfold flagMat flagB
  rw [← Matrix.smul_mul]
  congr 1
  ext j l
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, h, map_mul, map_pow, smul_eq_mul]

theorem flagCoord_eq [Fintype S] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type} (x : κ → Ω) {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (k : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc (k, J) = algebraMap Ω (GenField Ω r) (x k) *
      ∏ q : (Σ s, Fin (r s)), ((algebraMap Ω (GenField Ω r) a ^ m q.1) ^ ((q.2 : ℕ) + 1) *
        stepMinor (flagB M T q.1) q.2 (J q)) := by
  unfold flagCoord
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  have := stepMinor_smul (algebraMap Ω (GenField Ω r) a ^ m q.1) (flagB M T q.1) q.2 (J q)
  rw [← this, ← flagMat_eq h q.1]
  rfl

theorem prod_update_div {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type} {F : Type} [Field F]
    (f : ∀ q, β q → F) (J : ∀ q, β q) (h : ∀ q, f q (J q) ≠ 0) (q : ι) (b : β q) :
    (∏ q', f q' (Function.update J q b q')) / (∏ q', f q' (J q')) = f q b / f q (J q) := by
  have h1 : ∏ q', f q' (Function.update J q b q') =
      f q b * ∏ q' ∈ Finset.univ.erase q, f q' (J q') := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun q' hq' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
  have h2 : ∏ q', f q' (J q') = f q (J q) * ∏ q' ∈ Finset.univ.erase q, f q' (J q') :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)).symm
  have h3 : ∏ q' ∈ Finset.univ.erase q, f q' (J q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h q'
  rw [h1, h2]
  field_simp [h q, h3]

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

theorem twist_left_inverse : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m n r : ℕ) (φ : Fin n → Module.Dual Ω E),
    IsTwistGen ξ x L m φ → ∀ (p : Cpt ξ) (c₁ : κ), InChart ξ x c₁ p → ∀ β : Fin r → E, L.IsFrameAt β p →
    ∃ B : Matrix (Fin r) (Fin n) Ω, (∀ a j, B a j ∈ regAt ξ p) ∧ (∀ j a, φ j (β a) / x c₁ ^ m ∈ regAt ξ p) ∧
      B * Matrix.of (fun j a => φ j (β a) / x c₁ ^ m) = 1 := by
  intro X Ω _ ξ E _ _ κ x L m n r φ hT p c₁ hc β hβ
  have hβmem : ∀ a, β a ∈ L p := fun a => by
    rw [hβ.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hw : ∀ a : Fin r, ∃ w : Module.Dual Ω E, ∀ b, w (β b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hβ.1).coord a)
    refine ⟨g, fun b => ?_⟩
    have h1 : g (β b) = ((Module.Basis.span hβ.1).coord a) ((Module.Basis.span hβ.1) b) := by
      rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : a = b
    · subst h
      simp
    · simp [Finsupp.single_apply, h, Ne.symm h]
  choose w hw using hw
  have hwR : ∀ a, ∀ e ∈ L p, w a e ∈ regAt ξ p := by
    intro a e he
    rw [hβ.2] at he
    induction he using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [hw]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact add_mem hy hz
    | smul s y _ hy =>
      rw [Subring.smul_def, map_smul, smul_eq_mul]
      exact mul_mem s.2 hy
  have hg := fun a => hT.2 p c₁ hc (w a) (hwR a)
  choose g hgR hgw using hg
  refine ⟨Matrix.of fun a j => g a j, fun a j => hgR a j, fun j a => hT.1 j p c₁ hc (β a) (hβmem a), ?_⟩
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [← hgw a (β b) (hβmem b), hw]

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem _root_.GlobalTheory.T.local_index_at_single_place : ∀ (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 → (∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) → (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup = B.toAddSubgroup.relIndex A.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt <;> assumption)
end

section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem _root_.GlobalTheory.T.glued_lattice_finite_index : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → (glued T).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧ (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (glued T).toAddSubgroup ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem isLocalizationAway_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω}
    (hg : g ∈ A) (h0 : g ≠ 0) :
    letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
    IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := by
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A (invAdj A g) a : invAdj A g) : Ω) = a := fun _ => rfl
  refine IsLocalization.Away.mk (⟨g, hg⟩ : A) ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) (Subtype.ext ?_)
    simp [hmap, h0]
  · intro s
    obtain ⟨k, hk⟩ := exists_mul_pow_mem hg h0 s.2
    refine ⟨k, ⟨_, hk⟩, Subtype.ext ?_⟩
    simp [hmap]
  · intro a b hab
    have hab' : a = b := Subtype.ext (by simpa [hmap] using congrArg Subtype.val hab)
    exact ⟨0, by rw [hab']⟩

theorem smooth_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 →
    Algebra.Smooth ℚ A → Algebra.Smooth ℚ (invAdj A g) := by
  intro Ω _ _ A g hg h0 hA
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ A (invAdj A g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := isLocalizationAway_invAdj hg h0
  haveI : Algebra.Smooth A (invAdj A g) := Algebra.Smooth.of_isLocalization_Away (⟨g, hg⟩ : A)
  exact Algebra.Smooth.comp ℚ A (invAdj A g)

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
