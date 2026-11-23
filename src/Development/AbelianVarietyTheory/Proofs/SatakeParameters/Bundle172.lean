module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle004
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle009
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle166
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix

namespace GlobalTheory.Hk3

theorem locVac_mem_span_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ w : M, GlobalTheory.Hk3.LocVac ρ w → w ∈ Submodule.span ℂ {s} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac hspan w hw
  classical
  have hind := locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) s = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x s := by
    intro x u hu
    have h1 : ρ x s = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) s := by
      have := congrArg (fun f => f s) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x s) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x s := by
    intro x u hu
    have := congrArg (fun f => f s) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  set Λ := HoweDuality.intMat L n' n with hΛdef
  set V : Matrix (Fin n') (Fin n) L ⧸ Λ → Submodule ℂ M := fun c => Submodule.span ℂ {ρ c.out s} with hVdef
  have hVind : iSupIndep V := by
    refine hind.mono fun c => Submodule.span_le.mpr ?_
    rintro _ rfl
    exact Submodule.subset_span ⟨c.out, QuotientAddGroup.out_eq' c, rfl⟩
  have hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x) := by
    intro x
    have hm : -(QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq'])
    have := hshift (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out _ hm
    rw [add_neg_cancel_left] at this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hwV : w ∈ ⨆ c, V c := by
    have hle : Submodule.span ℂ (Set.range fun x => ρ x s) ≤ ⨆ c, V c :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact Submodule.mem_iSup_of_mem _ (hmemV x))
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨f, hf, hfw⟩ := (Submodule.mem_iSup_iff_exists_finsupp V w).mp hwV
  set χ : Matrix (Fin n') (Fin n) L ⧸ Λ → Matrix (Fin n') (Fin n) L → ℂ :=
    fun c u => ψ (locH σ δ JS JT u c.out + σ (locH σ δ JS JT u c.out)) with hχ
  have heigV : ∀ c, ∀ u ∈ intMatSub (L := L) n n', ∀ v ∈ V c, ρ u v = χ c u • v := by
    intro c u hu v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, heig _ u hu, smul_comm]
  have hzero : ∀ c, c ≠ 0 → f c = 0 := by
    intro c hc
    obtain ⟨u, hu, hχu⟩ : ∃ u ∈ intMatSub (L := L) n n', χ c u ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hint := intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne c.out hcon
      apply hc
      rw [hΛ] at hint
      rw [← QuotientAddGroup.out_eq' c, QuotientAddGroup.eq_zero_iff]
      exact hint
    have hsum : (f.support.sum fun d => (χ d u - 1) • f d) = 0 := by
      have e1 : ρ u w = f.support.sum fun d => χ d u • f d := by

        rw [← hfw, Finsupp.sum, map_sum]
        exact Finset.sum_congr rfl fun d _ => heigV d u hu _ (hf d)
      have e2 : w = f.support.sum fun d => f d := by rw [← hfw, Finsupp.sum]
      simp only [sub_smul, one_smul, Finset.sum_sub_distrib, ← e1, ← e2, hw u hu, sub_self]
    by_cases hcs : c ∈ f.support
    · rw [← Finset.add_sum_erase _ _ hcs, add_eq_zero_iff_eq_neg] at hsum
      have hmem1 : (χ c u - 1) • f c ∈ V c := Submodule.smul_mem _ _ (hf c)
      have hmem2 : (χ c u - 1) • f c ∈ ⨆ (j) (_ : j ≠ c), V j := by
        rw [hsum]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => ?_)
        have hdc : d ≠ c := Finset.ne_of_mem_erase hd
        exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hdc (Submodule.smul_mem _ _ (hf d)))
      have hz : (χ c u - 1) • f c = 0 := by
        have := (iSupIndep_def.mp hVind c)
        rw [Submodule.disjoint_def] at this
        exact this _ hmem1 hmem2
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχu)
    · exact Finsupp.notMem_support_iff.mp hcs
  have hw0 : w = f 0 := by
    rw [← hfw, Finsupp.sum, Finset.sum_eq_single (0 : Matrix (Fin n') (Fin n) L ⧸ Λ)]
    · intro d _ hd; exact hzero d hd
    · intro h0; exact Finsupp.notMem_support_iff.mp h0
  have hout : ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s = s := by
    apply hvac
    have : (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out ∈ Λ := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
    exact this
  have := hf 0
  change f 0 ∈ Submodule.span ℂ {ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s} at this
  rw [hout] at this
  rw [hw0]; exact this

end GlobalTheory.Hk3
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct Matrix

namespace GlobalTheory.TwV.LbB

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p n : ℕ} {G : GAtP p}

def FrAtB (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, ((((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ t) a ∈ (A.pl v).1.adicCompletionIntegers F

def IntB (A : LocAt F E n G) (v : Fin G.P.nV) (t : Fin n → G.P.Qq v) : Prop :=
  ∀ a, ((((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
    Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ (fun k => A.eQ v (t k))) a ∈ (A.pl v).1.adicCompletionIntegers F

theorem intB_zero (A : LocAt F E n G) (v : Fin G.P.nV) : IntB A v 0 := by
  intro a
  have : (fun k => A.eQ v ((0 : Fin n → G.P.Qq v) k)) = 0 := by funext k; simp
  rw [this, Matrix.mulVec_zero]
  exact zero_mem _

theorem intB_add (A : LocAt F E n G) (v : Fin G.P.nV) (t t' : Fin n → G.P.Qq v) (h : IntB A v t) (h' : IntB A v t') :
    IntB A v (t + t') := by
  intro a
  have : (fun k => A.eQ v ((t + t') k)) = (fun k => A.eQ v (t k)) + (fun k => A.eQ v (t' k)) := by funext k; simp
  rw [this, Matrix.mulVec_add]
  exact add_mem (h a) (h' a)

theorem intB_smul (A : LocAt F E n G) (hW : LocInt A) (v : Fin G.P.nV) (c : G.P.W v) (t : Fin n → G.P.Qq v) (h : IntB A v t) :
    IntB A v (c • t) := by
  intro a
  have : (fun k => A.eQ v ((c • t) k)) = A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) c) • (fun k => A.eQ v (t k)) := by
    funext k
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl
  rw [this, Matrix.mulVec_smul]
  exact mul_mem ((hW v _).1 ⟨c, rfl⟩) (h a)

theorem mulVec_inv_mulVec {R : Type} [CommRing R] (y : GL (Fin n) R) (u : Fin n → R) :
    (y : Matrix (Fin n) (Fin n) R) *ᵥ (((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mem_colSpan {Qq W : Type} [CommRing W] [Field Qq] [Algebra W Qq] (M : Matrix (Fin n) (Fin n) Qq) (r : Fin n → W) :
    M *ᵥ (fun c => algebraMap W Qq (r c)) ∈ colSpan W M := by
  have : M *ᵥ (fun c => algebraMap W Qq (r c)) = ∑ c, r c • (fun i => M i c) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem fst_mem_span (A : LocAt F E n G) (hW : LocInt A)
    (hAlg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a)) (v : Fin G.P.nV)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F)
    (hx : x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb) :
    (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) ∈
      Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) := by
  unfold Formalism.L2.Herm.locL latS at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun a => (A.eQ v).symm ((A.spl v ((0 : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F) a)).1)) = 0 := by
      funext a; simp
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun a => (A.eQ v).symm ((A.spl v ((x + y) a)).1)) =
        (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) + (fun a => (A.eQ v).symm ((A.spl v (y a)).1)) := by
      funext a; simp
    rw [this]
    exact Submodule.add_mem _ hx hy
  | smul s x _ hx =>
    have hs := (split_integral_completion F E (A.pl v).1 (A.spl v) (hAlg v) s).1 s.2
    obtain ⟨c, hc⟩ := (hW v ((A.eQ v).symm ((A.spl v s).1))).2 (by rw [RingEquiv.apply_symm_apply]; exact hs.1)
    have : (fun a => (A.eQ v).symm ((A.spl v ((s • x) a)).1)) = c • (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) := by
      funext a
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul, map_mul, Pi.smul_apply, Algebra.smul_def, hc]
    rw [this]
    exact Submodule.smul_mem _ c hx



theorem lbAt_gen (A : LocAt F E n G) (hW : LocInt A)
    (hAlg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfr : FrAtB A Lb) (v : Fin G.P.nV) :
    Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) =
      colSpan (G.P.W v) ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) := by
  set fr : GL (Fin n) ((A.pl v).1.adicCompletion F) := bc (A.phE v) A.B with hfrdef
  have hM : ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) =
      (fr : Matrix (Fin n) (Fin n) _).map ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) := by
    ext a b; rfl

  have h1 : ∀ t ∈ Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))), IntB A v t := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      have hloc : (fun k => inclE (F := F) ((A.pl v).1.adicCompletion F) (y k)) ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      have := (hfr v (fun k => A.eQ v (A.iw v (y k)))).1 ⟨_, hloc, fun a => by
        show (A.ph v) (inclE (F := F) ((A.pl v).1.adicCompletion F) (y a)) = A.eQ v ((A.eQ v).symm (A.phE v (y a)))
        rw [RingEquiv.apply_symm_apply]
        rfl⟩
      exact this
    | zero => exact intB_zero A v
    | add x y _ _ hx hy => exact intB_add A v x y hx hy
    | smul c x _ hx => exact intB_smul A hW v c x hx

  have h2 : ∀ t, IntB A v t → ∃ r : Fin n → G.P.W v,
      t = ((fr : Matrix (Fin n) (Fin n) _).map ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v)) *ᵥ
        (fun c => algebraMap (G.P.W v) (G.P.Qq v) (r c)) := by
    intro t ht
    choose r hr using fun c => (hW v ((A.eQ v).symm ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => A.eQ v (t k))) c))).2 (by rw [RingEquiv.apply_symm_apply]; exact ht c)
    refine ⟨r, ?_⟩
    have e1 : (fun c => algebraMap (G.P.W v) (G.P.Qq v) (r c)) =
        fun c => (A.eQ v).symm ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => A.eQ v (t k))) c) := by
      funext c; exact hr c
    rw [e1]
    funext i
    have e2 := RingHom.map_mulVec ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (fr : Matrix (Fin n) (Fin n) _)
      (((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => A.eQ v (t k))) i
    rw [mulVec_inv_mulVec] at e2
    exact (RingEquiv.symm_apply_apply (A.eQ v) (t i)).symm.trans e2

  have h3 : ∀ t, IntB A v t →
      t ∈ Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) := by
    intro t ht
    obtain ⟨x, hx, hxa⟩ := (hfr v (fun k => A.eQ v (t k))).2 ht
    have h4 := fst_mem_span A hW hAlg v Lb x hx
    have e3 : (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) = t := by
      funext a; rw [hxa a]; exact RingEquiv.symm_apply_apply _ _
    rw [e3] at h4
    exact h4
  apply le_antisymm
  · intro t ht
    obtain ⟨r, rfl⟩ := h2 t (h1 t ht)
    rw [hM]
    exact mulVec_mem_colSpan _ r
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    apply h3
    intro a
    have hcol : (fun k => A.eQ v ((((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))) k c)) =
        fun k => (fr : Matrix (Fin n) (Fin n) _) k c := by
      funext k; rw [hM, Matrix.map_apply]; exact RingEquiv.apply_symm_apply _ _
    show ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ
      (fun k => A.eQ v ((((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))) k c))) a ∈ _
    rw [hcol]
    have e4 : (((fr⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ
        fun k => (fr : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) k c) a =
        ((((fr⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *
          (fr : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) a c) := by
      simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [e4, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem frAtB_re [StarRing E] {r N : ℕ} (h : r = N) (A : LocAt F E N G) (Lb : Submodule (𝓞 E) (Fin r → E)) (B0 : GL (Fin r) E)
    (hB : A.B = Formalism.L2.Forms.reGL h E B0) (fr : ∀ v, GL (Fin r) ((A.pl v).1.adicCompletion F))
    (hfr0 : ∀ v (t : Fin r → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
        ∀ a, ((((fr v)⁻¹ : GL (Fin r) ((A.pl v).1.adicCompletion F)) :
          Matrix (Fin r) (Fin r) ((A.pl v).1.adicCompletion F)) *ᵥ t) a ∈ (A.pl v).1.adicCompletionIntegers F)
    (hrat : ∀ v, fr v = bc (A.phE v) B0) :
    FrAtB A (Lb.map (((reE (E := E) h : (Fin r → E) ≃ₗ[E] (Fin N → E)) : (Fin r → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E))) := by
  subst h
  rw [Formalism.MainNotions.G.KAat.map_reE_rfl]
  have hre : Formalism.L2.Forms.reGL (rfl : r = r) E B0 = B0 := by apply Units.ext; ext a b; rfl
  rw [hre] at hB
  intro v t
  rw [hB, ← hrat v]
  exact hfr0 v t

end Gen

section Of

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p n : ℕ} {G : GAtP p}

theorem lbAtB_of (A : LocAt F E n G) (hW : LocInt A) (hAlg : SplAlg A)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfr : FrAtB A Lb) : GlobalTheory.TwV.LbAtB A Lb := by
  intro v
  unfold GlobalTheory.TwV.locSp
  exact lbAt_gen A hW hAlg Lb hfr v

end Of

end GlobalTheory.TwV.LbB

end
end

section

noncomputable section

namespace GlobalTheory.TwU.RatNorm

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

variable {p : ℕ} [Fact p.Prime]

theorem frob_pow_int (X : Sys p) (v : X.Pl) (k : ℕ) (x : X.G.P.W v) :
    ∃ y : X.G.P.W v, (X.G.P.σ v ^ k) (algebraMap _ _ x) = algebraMap _ _ y := by
  induction k generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
    obtain ⟨z, hz⟩ := ih (x ^ p + (p : X.G.P.W v) * y)
    refine ⟨z, ?_⟩
    rw [pow_succ]
    show (X.G.P.σ v ^ k) ((X.G.P.σ v) (algebraMap _ _ x)) = _
    rw [hy, hz]

theorem norm_twG_int_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.G.P.W v) :
    ‖twG X E v s (algebraMap _ _ x)‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := frob_pow_int X v s.val x
  have h := E.int (X.G.P.j v y)
  unfold twG
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [hy, (X.G.P.setting v).ι_comp]
  exact h

theorem norm_twG_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (u : (X.G.P.W v)ˣ) :
    ‖twG X E v s (algebraMap _ _ (u : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_int_le X E v s (u : X.G.P.W v)
  have h2 := norm_twG_int_le X E v s ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have h3 : twG X E v s (algebraMap _ _ (u : X.G.P.W v)) * twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg (twG X E v s (algebraMap _ _ (u : X.G.P.W v))),
    norm_nonneg (twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) {y : X.G.P.Qq v} (hy : y ≠ 0) :
    ‖twG X E v s y‖ = ‖(p : ℂ_[p])‖ ^ ordP (X.G.P.W v) p y := by
  haveI := (X.G.P.setting v).frac_alt
  have hp := (X.G.P.setting v).p_unif
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hp hy
  rw [ordP_eq hp n u, map_mul, map_zpow₀, map_natCast, norm_mul, norm_twG_unit, one_mul, norm_zpow]

theorem zpow_sum_fin {ι : Type*} (s : Finset ι) (r : ℝ) (hr : r ≠ 0) (f : ι → ℤ) :
    r ^ (∑ i ∈ s, f i) = ∏ i ∈ s, r ^ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hr, ih]

theorem norm_lamC_type_normOne : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v),
    LamPos X E pos lam ρ → ∀ (e : D.what₂.Tau → ℤ) (z : D.host.E), z * D.host.conj z = 1 →
    ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ)‖ =
      ‖(p : ℂ_[p])‖ ^ (∑ v : X.Pl, (∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩)) *
        ordP (X.G.P.W v) p (ρ v z)) := by
  intro D p _ X E pos lam ρ hL e z hz
  have hp0 : ‖(p : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hmem : ∀ τ, TaylorLogMetric.embT D τ z ∈ TaylorLogMetric.Qbar := fun τ =>
    (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  have hprod : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => zpow_mem (hmem τ) _
  have h1 : TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) = ∏ τ, TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ z) ^ e τ := by
    have e1 : (⟨∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ, hprod⟩ : TaylorLogMetric.Qbar) = ∏ τ, (⟨TaylorLogMetric.embT D τ z, hmem τ⟩ : TaylorLogMetric.Qbar) ^ e τ := by
      apply Subtype.ext
      push_cast
      rfl
    unfold TaylorLogMetric.lamC
    rw [dite_eq_left hprod, e1, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [dite_eq_left (hmem τ), map_zpow₀]
  have hρ : ∀ v, ρ v z * ρ v (D.host.conj z) = 1 := fun v => by rw [← map_mul, hz, map_one]
  have hρ0 : ∀ v, ρ v z ≠ 0 := fun v h => by have := hρ v; rw [h, zero_mul] at this; exact zero_ne_one this
  have hf : ∀ v s, ‖TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) z)‖ ^ e (pos ⟨v, s⟩) =
      ‖(p : ℂ_[p])‖ ^ ((if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩) * ordP (X.G.P.W v) p (ρ v z)) := by
    intro v s
    by_cases hs : IsOddPos s
    · rw [LamPos.odd X E pos lam ρ hL v s hs, if_pos hs, eq_inv_of_mul_eq_one_right (hρ v), map_inv₀, norm_inv, norm_twG X E v s (hρ0 v),
        inv_zpow', ← zpow_mul]
      congr 1
      ring
    · rw [LamPos.even X E pos lam ρ hL v s hs, if_neg hs, norm_twG X E v s (hρ0 v), ← zpow_mul]
      congr 1
      ring
  rw [h1, norm_prod]
  simp_rw [norm_zpow]
  rw [← Equiv.prod_comp pos, Fintype.prod_sigma]
  simp_rw [hf, Finset.sum_mul]
  rw [zpow_sum_fin _ _ hp0]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [zpow_sum_fin _ _ hp0]

end GlobalTheory.TwU.RatNorm

end
end

section

open Matrix

theorem _root_.GlobalTheory.T.integral_of_traceCharPairing_skewHermitian : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ),
  Formalism.UG.IsUnramInv ϖ σ q → (Valued.v δ = 1 ∧ σ δ = -δ) →
  (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
  ∀ (r : ℕ) (e : Fin r → ℕ) (Δ : Matrix (Fin r) (Fin r) L), (∀ j k, σ (Δ j k) = Δ k j) →
  (∀ Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e, ψ (δ * Matrix.trace (Γ * Δ)) = 1) →
  ∀ j k, Δ j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.GramSep.int_of_psi_trace_gam | exact GlobalTheory.Hk3.GramSep.int_of_psi_trace_gam | (intros; apply GlobalTheory.Hk3.GramSep.int_of_psi_trace_gam <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isSplitPlaceBelowCMField_of_sqrt_neg_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  first | exact @GlobalTheory.SplitOfNegPrime.isSplitAt | exact GlobalTheory.SplitOfNegPrime.isSplitAt | (intros; apply GlobalTheory.SplitOfNegPrime.isSplitAt <;> assumption)
end
