module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Formalism.HermitianLattices.StatementLat
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle079
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
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
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

@[expose] public section

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem mem_levelVL_of_first_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (L : Submodule (𝓞 E) (Fin n → E)), SelfDualAt cm.sig J v L → ∀ κ ∈ UPts cm.sig J (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = ((bc ((RingHom.fst _ _).comp sp.toRingHom) κ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b) → κ ∈ levelVL cm.sig J v L := by
  intro F E _ _ _ _ _ _ cm n J v sp hsig hdiag L hsd κ hκ hfirst
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag

  have pair1 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).1 =
      ∑ i, ∑ j, (sp (z i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
    intro z y
    unfold hR hform

    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have pair2 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).2 =
      ∑ i, ∑ j, (sp (z i)).1 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).2 * (sp (y j)).2 := by
    intro z y
    unfold hR hform

    rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl

  have hprod : ∀ y : Fin n → E ⊗[F] v.adicCompletion F, y ∈ loc v L ↔
      (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2 := by
    intro y
    refine ⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩
    rintro ⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩
    have ha : sp.symm (1, 0) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
    have hb : sp.symm (0, 1) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩
    have hm := (loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)
    have hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂ := by
      funext b
      apply sp.injective
      change sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)
      rw [map_add (f := _), map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      ext
      · simp [e₁ b]
      · simp [e₂ b]
    rw [hy]; exact hm

  set Kv := v.adicCompletion F with hKv
  set φ1 : E ⊗[F] Kv →+* Kv := (RingHom.fst _ _).comp sp.toRingHom with hφ1
  set φ2 : E ⊗[F] Kv →+* Kv := (RingHom.snd _ _).comp sp.toRingHom with hφ2
  have e1 : ∀ a, φ1 a = (sp a).1 := fun _ => rfl
  have e2 : ∀ a, φ2 a = (sp a).2 := fun _ => rfl
  set K1 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ1 with hK1
  set K2 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ2 with hK2
  set J2 : Matrix (Fin n) (Fin n) Kv := (J.map (inclE (F := F) Kv)).map φ2 with hJ2

  have hU : cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) * J.map (inclE (F := F) Kv) *
      (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) = J.map (inclE (F := F) Kv) := hκ
  have hc : (cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv))).map φ2 = K1ᵀ := by
    refine Matrix.ext fun i j => ?_
    show (sp (sigR cm.sig Kv ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i))).2 = (sp ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i)).1
    rw [hsig]; rfl
  have hU2 : K1ᵀ * J2 * K2 = J2 := by
    have := congrArg (fun M => M.map φ2) hU
    simp only [Matrix.map_mul] at this
    rw [hc] at this
    exact this
  have hQ : ∀ u w : Fin n → Kv, (K1 *ᵥ u) ⬝ᵥ (J2 *ᵥ (K2 *ᵥ w)) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    conv_rhs => rw [← hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hsum : ∀ u w : Fin n → Kv, (∑ i, ∑ j, u i * J2 i j * w j) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

  have hL2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∀ u : Fin n → Kv, (∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = u b) → u ⬝ᵥ (J2 *ᵥ w) ∈ v.adicCompletionIntegers F := by
    intro w
    constructor
    · rintro ⟨y, hy, ey⟩ u ⟨z, hz, ez⟩
      have h := ((hint _).1 (((hsd y).1 hy) z hz)).2
      rw [pair2] at h
      simp only [ez, ey] at h
      rw [← hsum]; exact h
    · intro h
      refine ⟨fun b => sp.symm (0, w b), ?_, fun b => by simp⟩
      refine (hsd _).2 fun z hz => (hint _).2 ⟨?_, ?_⟩
      · rw [pair1]; simp
      · rw [pair2]
        have := h (fun b => (sp (z b)).1) ⟨z, hz, fun _ => rfl⟩
        rw [← hsum] at this
        have e : ∀ j, (sp (sp.symm (0, w j))).2 = w j := fun j => by simp
        simp only [e]
        exact this

  have hH : ∀ x : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = (K1 *ᵥ x) b := hfirst
  have hK1inv : ∀ u : Fin n → Kv, ∃ u', K1 *ᵥ u' = u := by
    intro u
    refine ⟨(((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) *ᵥ u, ?_⟩
    rw [Matrix.mulVec_mulVec]
    have : K1 * (((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) = 1 := by
      have := (bc φ1 κ).mul_inv
      exact this
    rw [this, Matrix.one_mulVec]
  have hK2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = (K2 *ᵥ w) b := by
    intro w
    rw [hL2, hL2]
    constructor
    · intro h u hu
      obtain ⟨u', rfl⟩ := hK1inv u
      rw [hQ]
      exact h u' ((hH u').2 hu)
    · intro h u hu
      rw [← hQ]
      exact h _ ((hH u).1 hu)

  have hc1 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).1 =
      (K1 *ᵥ fun j => (sp (x j)).1) b := by
    intro x b

    simp only [mulVec, dotProduct, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]
    rfl
  have hc2 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).2 =
      (K2 *ᵥ fun j => (sp (x j)).2) b := by
    intro x b

    simp only [mulVec, dotProduct, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]
    rfl
  show κ ∈ UJ _ _ ⊓ stabGL _
  rw [Subgroup.mem_inf]
  refine ⟨hκ, fun x => ?_⟩
  change x ∈ loc v L ↔ _ ∈ loc v L
  rw [hprod x, hprod (_ *ᵥ x)]
  simp only [hc1, hc2]
  rw [hH (fun j => (sp (x j)).1), hK2 (fun j => (sp (x j)).2)]

end GlobalTheory.St.G
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdStab

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_eq_one (hG : Good S) : S.th = 1 := by
  simp [Frames.th, hG.gg]

theorem image_all (g : Fin (r + 1) → S.V) :
    g '' {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.range g := by
  rw [show {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ from
    Set.eq_univ_of_forall fun i => i.is_lt, Set.image_univ]

theorem mem_span_iff (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V)
    (hA : S.IsInner g gs A) (x : S.V) :
    x ∈ Submodule.span L.O (Set.range g) ↔ x ∈ S.stdLat g gs A ∧ x ∈ S.spanTo g (r + 1) := by
  rw [← image_all S g]
  exact ((GlobalTheory.HL.StdLat.stdLat_spec L r k S g gs hg A hA).2.1 (r + 1) le_rfl x).symm

theorem inv_apply_apply (h : S.GLV) (x : S.V) : h⁻¹ (h x) = x :=
  h.symm_apply_apply x

end

theorem stab_coordLat : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → S.a = 0 → ∀ d₀, S.IsTermW d₀ (coordLat S) 1 1 → S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hG ha d₀ hT
  have hTerm : S.IsTerm d₀ (coordLat S) := ⟨(1, 1), hT⟩
  have hMeq := (GlobalTheory.HL.WitIndep.witness_independence L r k S d₀ (coordLat S) 1 1 hT).2.1
  obtain ⟨hA, hA', -, -, hC1, hC2, -, -⟩ := hT
  rw [one_smul] at hC1 hC2
  have hf : ∀ x, x ∈ Submodule.span L.O (Set.range S.f) ↔
      x ∈ coordLat S ∧ x ∈ S.spanTo S.f (r + 1) := by
    intro x; rw [hC1]; exact mem_span_iff S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA x
  have hf' : ∀ x, x ∈ Submodule.span L.O (Set.range S.f') ↔
      x ∈ coordLat S ∧ x ∈ S.spanTo S.f' (r + 1) := by
    intro x; rw [hC2]; exact mem_span_iff S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA' x
  have th1 := th_eq_one S hG

  have key1 : ∀ h ∈ S.St, h • coordLat S = coordLat S → ∀ x,
      (x ∈ Submodule.span L.O (Set.range S.f) → h x ∈ Submodule.span L.O (Set.range S.f)) ∧
      (x ∈ Submodule.span L.O (Set.range S.f') → h x ∈ Submodule.span L.O (Set.range S.f')) := by
    intro h hh hC x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [hf] at hx ⊢
      refine ⟨?_, (GlobalTheory.FrameAct.spanTo_iff S h hh _ x).2 hx.2⟩
      rw [← hC]; exact (GlobalTheory.FrameAct.mem_smul_iff S h _ x).2 hx.1
    · rw [hf'] at hx ⊢
      refine ⟨?_, (GlobalTheory.FrameAct.spanTo_iff' S h hh _ x).2 hx.2⟩
      rw [← hC]; exact (GlobalTheory.FrameAct.mem_smul_iff S h _ x).2 hx.1

  have key2 : ∀ g ∈ S.K0, ∀ x ∈ coordLat S, g x ∈ coordLat S := by
    intro g hg
    obtain ⟨⟨hgSt, hgf⟩, hgf'⟩ := hg
    replace hgf : g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) := hgf
    replace hgf' : g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') := hgf'
    replace hgSt : g ∈ S.St := hgSt
    have gf : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) →
        ∀ b, g (S.f b) ∈ coordLat S := by
      intro g hg b
      have h1 : g (S.f b) ∈ Submodule.span L.O (Set.range S.f) := by
        rw [← hg]; exact (GlobalTheory.FrameAct.mem_smul_iff S g _ _).2 (Submodule.subset_span ⟨b, rfl⟩)
      exact ((hf _).1 h1).1
    have gf' : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') →
        ∀ b, g (S.f' b) ∈ coordLat S := by
      intro g hg b
      have h1 : g (S.f' b) ∈ Submodule.span L.O (Set.range S.f') := by
        rw [← hg]; exact (GlobalTheory.FrameAct.mem_smul_iff S g _ _).2 (Submodule.subset_span ⟨b, rfl⟩)
      exact ((hf' _).1 h1).1
    have hM : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) →
        g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') →
        ∀ m ∈ S.Mof S.f S.f', g m ∈ coordLat S := by
      intro g h1 h2 m hm
      induction hm using Submodule.span_induction with
      | mem y hy =>
        rcases hy with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · exact gf g h1 b
        · simp only [th1, inv_one, map_one, one_smul, map_sub]
          exact (coordLat S).sub_mem (gf' g h2 b) (gf g h1 b)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact (coordLat S).add_mem hx hy
      | smul c x _ hx =>
        have e : g (c • x) = c • g x := by
          first
            | exact LinearEquiv.map_smul_of_tower g c x
            | exact g.toLinearMap.map_smul_of_tower c x
            | (rw [Subring.smul_def, map_smul, ← Subring.smul_def])
        rw [e]; exact (coordLat S).smul_mem c hx
    intro x hx
    obtain ⟨-, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
    have hx' : x ∈ S.ME ⊔ S.W0 := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    have hmM : m ∈ S.Mof S.f S.f' := by
      have := GlobalTheory.HL.UnimodTerm.proj_mem S hTerm ha hx hm (by simpa using hw)
      rw [hMeq] at this; exact this
    have hw' : w ∈ coordLat S := by
      have h1 := hM 1 (one_smul _ _) (one_smul _ _) m hmM
      have : w = (m + w) - m := by abel
      rw [this]; exact (coordLat S).sub_mem hx h1
    rw [map_add (f := _), (GlobalTheory.HL.FrameStab.stab_eq L r k S).1 g hgSt w hw]
    exact (coordLat S).add_mem (hM g hgf hgf' m hmM) hw'
  ext h
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Frames.K0]
  constructor
  · rintro ⟨hh, hC⟩
    have hC' : h⁻¹ • coordLat S = coordLat S := by rw [inv_smul_eq_iff]; exact hC.symm
    have hhi : h⁻¹ ∈ S.St := inv_mem hh
    refine ⟨⟨hh, ?_⟩, ?_⟩
    · refine (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, (key1 h hh hC x).1⟩).symm
      have := (key1 h⁻¹ hhi hC' (h x)).1 hx
      rwa [inv_apply_apply] at this
    · refine (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, (key1 h hh hC x).2⟩).symm
      have := (key1 h⁻¹ hhi hC' (h x)).2 hx
      rwa [inv_apply_apply] at this
  · rintro ⟨⟨hh, h1⟩, h2⟩
    have hK : h ∈ S.K0 := ⟨⟨hh, h1⟩, h2⟩
    refine ⟨hh, (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, key2 h hK x⟩).symm⟩
    have := key2 h⁻¹ (inv_mem hK) _ hx
    rwa [inv_apply_apply] at this

end GlobalTheory.HL.StdStab
end

section

open NumberField

namespace GlobalTheory

theorem hermLat_boundedScaleDual_finite {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (d c : ℕ) (hd : 0 < d) (hc : 0 < c) :
    ∃ s : Finset (Submodule (𝓞 K) V), (∀ M₀ ∈ s, Submodule.IsLattice K M₀) ∧
      ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
        (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) →
        (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) →
        ∃ M₀ ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M₀ = M := by
  classical
  let iQ : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  have hQs : ∀ (q : ℚ) (x : V), q • x = (algebraMap ℚ K q) • x := fun _ _ => rfl
  have : IsScalarTower ℚ K V := ⟨fun q a x => by rw [hQs, Algebra.smul_def, mul_smul]⟩
  have : FiniteDimensional ℚ V := Module.Finite.trans K V
  let B : LinearMap.BilinForm ℚ V := LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ K (h x y))
    (fun x₁ x₂ y => by simp only [map_add (f := _), LinearMap.add_apply])
    (fun q x y => by
      simp only [hQs, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        Formalism.HermitianLatticesTheory.traceReal_star_rat,
        Formalism.HermitianLatticesTheory.traceReal_trace_smul])
    (fun x y₁ y₂ => by simp only [map_add (f := _)])
    (fun q x y => by simp only [hQs, map_smul, smul_eq_mul,
      Formalism.HermitianLatticesTheory.traceReal_trace_smul])
  have hBS : LinearMap.IsSymm B := ⟨fun x y => by
    change Algebra.trace ℚ K (h x y) = Algebra.trace ℚ K (h y x)
    rw [← hs.eq x y, Formalism.HermitianLatticesTheory.traceReal_star]⟩
  have hfull : ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M →
      (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) →
      Submodule.IsFullLattice K M := by
    intro M hM hdual
    let : Submodule.IsLattice K M := hM
    let W : Submodule K V := Submodule.span K (M : Set V)
    let WQ : Submodule ℚ V := W.restrictScalars ℚ
    have hrestrict : (B.restrict WQ).Nondegenerate := by
      constructor
      · intro x hx
        apply Subtype.ext
        by_contra hn
        have hp := hpos (x : V) hn
        have hz := hx x
        change Algebra.trace ℚ K (h (x : V) (x : V)) = 0 at hz
        linarith
      · intro x hx
        apply Subtype.ext
        by_contra hn
        have hp := hpos (x : V) hn
        have hz := hx x
        change Algebra.trace ℚ K (h (x : V) (x : V)) = 0 at hz
        linarith
    have hortho : B.orthogonal WQ = ⊥ := by
      apply eq_bot_iff.mpr
      intro y hy
      have hyzero : ∀ x ∈ M, h x y = 0 := by
        intro x hx
        apply (traceForm_nondegenerate ℚ K).1
        intro a
        have hz := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) (star a • x)
          (show star a • x ∈ WQ from W.smul_mem _ (Submodule.subset_span hx))
        change Algebra.trace ℚ K (h (star a • x) y) = 0 at hz
        simpa only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          starRingEnd_apply, star_star, Algebra.traceForm_apply, mul_comm] using hz
      have hcy : (c : K) • y ∈ M := hdual y (fun x hx => ⟨0, by simp [hyzero x hx]⟩)
      have hz := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) ((c : K) • y)
        (show (c : K) • y ∈ WQ from Submodule.subset_span hcy)
      change Algebra.trace ℚ K (h ((c : K) • y) y) = 0 at hz
      simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, star_natCast] at hz
      rw [← map_natCast (algebraMap ℚ K) c, ← Algebra.smul_def, map_smul, smul_eq_mul] at hz
      have hcQ : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
      have hz' : Algebra.trace ℚ K (h y y) = 0 := (mul_eq_zero.mp hz).resolve_left hcQ
      have : y = 0 := by by_contra hn; have := hpos y hn; linarith
      simp [this]
    have htop : WQ = ⊤ := B.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot hBS.isRefl hrestrict hortho
    exact ⟨by apply eq_top_iff.mpr; intro x hx; exact (eq_top_iff.mp htop) (by trivial)⟩
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hs hpos
  set e : ℤ := NumberField.discr K with he
  have he0 : e ≠ 0 := NumberField.discr_ne_zero K
  have ecast : ((e.natAbs ^ 2 : ℕ) : K) = ((e : K)) * (e : K) := by
    have h0 : ((e.natAbs ^ 2 : ℕ) : ℤ) = e * e := by rw [Nat.cast_pow, Int.natAbs_sq, sq]
    rw [← Int.cast_natCast, h0, Int.cast_mul]
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) ∧
    (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M)}
  obtain ⟨s, hs1, hs2⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.final_shortVectors
    Formalism.HermitianLatticesTheory.final_finIntermediate Formalism.HermitianLatticesTheory.final_isomOfTrace h hpos N ι hι hmul d hd
    (Real.sqrt (((c * e.natAbs ^ 2 : ℕ) : ℝ) ^ N)) S
    (fun M hM x hx y hy => Submodule.mem_one.mpr (hM.2.1 x hx y hy))
    (fun M hM => hlat M (hfull M hM.1 hM.2.2))
    (by
      intro M hM _ _
      apply Formalism.HermitianLatticesTheory.genusCovolBound_covol_le h N ι hι M (c * e.natAbs ^ 2)
        (Nat.mul_pos hc (pow_pos (Int.natAbs_pos.mpr he0) 2))
      have hdual : ∀ y, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
          ∀ x ∈ M, h x ((e : K) • y) ∈ Set.range (algebraMap (𝓞 K) K) := by
        intro y hy x hx
        rw [LinearMap.map_smul, smul_eq_mul]
        have hm : ((e : ℤ) : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
          apply Formalism.HermitianLatticesTheory.genusCovolBound_discr
          intro r
          obtain ⟨s, hs'⟩ := hstar r
          obtain ⟨z, hz⟩ := hy (s • x) (M.smul_mem s hx)
          refine ⟨z, ?_⟩
          rw [← hz]
          congr 1
          rw [← algebraMap_smul K s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
            starRingEnd_apply, hs', star_star, mul_comm]
        exact Submodule.mem_one.mp hm
      intro y y' hy hy'
      have h1 : (c : K) • ((e : K) • y) ∈ M := hM.2.2 _ (hdual y hy)
      have h2 := hdual y' hy' _ h1
      have key : h ((c : K) • ((e : K) • y)) ((e : K) • y') =
          algebraMap ℚ K ((c * e.natAbs ^ 2 : ℕ) : ℚ) * h y y' := by
        rw [map_natCast, Nat.cast_mul, ecast]
        simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast,
          star_natCast, smul_eq_mul]
        ring
      rw [key] at h2
      obtain ⟨r, hr⟩ := h2
      obtain ⟨z, hz⟩ := Formalism.HermitianLatticesTheory.genusCovolBound_trace_int (K := K) r
      refine ⟨z, ?_⟩
      rw [← hz, hr, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
  exact ⟨s, fun M₀ hM₀ => (hs1 M₀ hM₀).1, fun M hL hd' hc' => hs2 M ⟨hL, hd', hc'⟩⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.localUnitaryGroup_tuples_topological_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  first | exact @GlobalTheory.LocalUnitaryTop.top_facts | exact GlobalTheory.LocalUnitaryTop.top_facts | (intros; apply GlobalTheory.LocalUnitaryTop.top_facts <;> assumption)
end
