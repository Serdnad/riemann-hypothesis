module

public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.GhostComponentG
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle147
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle152
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatIntFacts

theorem intValuation_uniformiser {R : Type} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R) {ϖ : R}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) : P.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

theorem exists_left_inverse {R : Type} [CommRing R] {n : ℕ} (ε : R) (B C : Matrix (Fin n) (Fin n) R)
    (hε : ε * ε = ε) (h : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) :
    ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have key : ∀ X Y : Matrix (Fin n) (Fin n) R,
      (ε • X + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * (ε • Y + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
        ε • (X * Y) + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    intro X Y
    have e1 : ε * (1 - ε) = 0 := by linear_combination -hε
    have e2 : (1 - ε) * ε = 0 := by linear_combination -hε
    have e3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
    simp only [add_mul, mul_add, smul_mul_smul_comm, hε, e1, e2, e3, zero_smul, mul_one, add_zero, zero_add]
  have h1 := key B C
  rw [h, ← add_smul, add_sub_cancel, one_smul] at h1
  have h2 := mul_eq_one_comm.1 h1
  rw [key] at h2
  rw [eq_sub_of_add_eq h2, sub_smul, one_smul, sub_sub_cancel]



theorem int_facts : ∀ {D : D7} (V : HSp D), (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ n : ℤ, finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n)) ∈ intAE D) ∧ ∀ (ε : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ε * ε = ε → (∀ y ∈ LamHat V, ∃ z, (fun a => ε * y a) = fun a => ε * B.mulVec z a) → ∃ C : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), ε • (B * C) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ε • (C * B) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V
  refine ⟨GlobalTheory.LatDual.smul_mem_lamHat V, ?_, ?_⟩
  · intro P e ϖ ϖ' he h1 h2 h1' h2' n
    have hv : P.valuation D.host.E ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n) ≤ 1 := by
      have v1 : P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ).trans (intValuation_uniformiser P h1 h2)
      have v2 : P.valuation D.host.E (ϖ' : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ').trans (intValuation_uniformiser P h1' h2')
      rw [map_div₀, map_zpow₀, map_zpow₀, v1, v2]
      exact div_self_le_one _
    obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
    have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
    have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
    have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
    have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
      by_contra hc
      exact hb ((he.2 _ hb0).2 hc)
    have hq : (ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hb1]
      exact hab
    have ha : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨1, fun v => one_mem _, a, rfl⟩
    have hm : ∀ {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
      intro x y hx hy
      refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
        refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
        · rw [map_mul]; exact mul_mem (ha w) (hb w)
        · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
      · intro x _; rw [zero_mul]; exact zero_mem _
      · intro x _; rw [mul_zero]; exact zero_mem _
      · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
      · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
      · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
      · intro x y _ _ h; rw [mul_neg]; exact neg_mem h
    have := hm ha hi
    rw [RingHom.map_mul, mul_left_comm] at this
    rw [hq, RingHom.map_mul, RingHom.map_mul]
    exact this
  · intro ε B hε h
    obtain ⟨-, -, -, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
    have hx : ∀ x : Fin V.rank → D.host.E, ∃ z, ∀ a,
        ε * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) = ε * B.mulVec z a := by
      intro x
      have hx : x ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
        rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz⟩ := h (fun a => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) (by
          rw [GlobalTheory.LatDual.lamHat_eq_hat]
          exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩)
        exact ⟨z, congrFun hz⟩
      | zero => exact ⟨0, fun a => by simp⟩
      | add u w _ _ hu hw =>
        obtain ⟨z, hz⟩ := hu
        obtain ⟨z', hz'⟩ := hw
        exact ⟨z + z', fun a => by
          rw [Pi.add_apply, TensorProduct.tmul_add, mul_add, hz, hz', Matrix.mulVec_add, Pi.add_apply, mul_add]⟩
      | smul c u _ hu =>
        obtain ⟨z, hz⟩ := hu
        refine ⟨((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) • z, fun a => ?_⟩
        rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ← hz,
          mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    choose z hz using hx
    have hBC : ε • (B * Matrix.of fun j i => z (Pi.single i 1) j) =
        ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
      refine Matrix.ext fun a i => ?_
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      refine (hz (Pi.single i 1) a).symm.trans ?_
      congr 1
      by_cases hai : a = i
      · subst hai
        rw [Pi.single_eq_same, Matrix.one_apply_eq]; rfl
      · rw [Pi.single_eq_of_ne hai, Matrix.one_apply_ne hai, TensorProduct.tmul_zero]
    exact ⟨_, hBC, exists_left_inverse ε B _ hε hBC⟩

end GlobalTheory.LatIntFacts
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open Formalism.L2.Col
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.HeckeLifts₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

abbrev SysL (A3 : FamIn3 K G Pl0 I0 Ty T m) (j : Fin m) (p : A3.fam3.base3.Ix) :
    ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) → Prop :=
  cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1))

end Abstract

section TwEig

variable {s : Bool} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tw_map_mul (a b : Module.End ℂ E) : (Tw.map s (a * b) : Module.End ℂ (Tw s E)) = Tw.map s a * Tw.map s b :=
  LinearMap.ext fun _ => rfl

theorem tw_map_pow (a : Module.End ℂ E) (k : ℕ) : (Tw.map s (a ^ k) : Module.End ℂ (Tw s E)) = Tw.map s a ^ k := by
  induction k with
  | zero => exact LinearMap.ext fun _ => rfl
  | succ k ih => rw [pow_succ, tw_map_mul, ih, pow_succ]

theorem tw_map_sub_smul (a : Module.End ℂ E) (μ : ℂ) :
    (Tw.map s a - μ • 1 : Module.End ℂ (Tw s E)) = Tw.map s (a - cj s μ • 1) :=
  LinearMap.ext fun _ => rfl

theorem mem_maxGen_tw (a : Module.End ℂ E) (μ : ℂ) (v : Tw s E) :
    v ∈ Module.End.maxGenEigenspace (Tw.map s a : Module.End ℂ (Tw s E)) μ ↔ Tw.out v ∈ a.maxGenEigenspace (cj s μ) := by
  simp only [Module.End.mem_maxGenEigenspace]
  rw [tw_map_sub_smul]
  refine exists_congr fun k => ?_
  rw [← tw_map_pow]
  exact Iff.rfl

theorem eigAt_tw {I : Type} (h : I → Module.End ℂ E) (y : I → ℂ) :
    eigAt (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) y = Tw.sub s (eigAt h fun i => cj s (y i)) := by
  refine SetLike.ext fun v => ?_
  rw [show v ∈ Tw.sub s (eigAt h fun i => cj s (y i)) ↔ Tw.out v ∈ eigAt h (fun i => cj s (y i)) from Iff.rfl]
  simp only [eigAt, Submodule.mem_iInf]
  exact forall_congr' fun i => mem_maxGen_tw (h i) (y i) v

theorem sub_iSup {ι : Type} (V : ι → Submodule ℂ E) : Tw.sub s (⨆ c, V c) = ⨆ c, Tw.sub s (V c) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun c v hv => (le_iSup V c) hv)
  exact Submodule.iSup_induction V (motive := fun y => (Tw.mk s y : Tw s E) ∈ ⨆ c, Tw.sub s (V c)) hx
    (fun c y hy => Submodule.mem_iSup_of_mem c hy) (zero_mem _) (fun a b ha hb => add_mem ha hb)

theorem sub_iSup_prop {P : Prop} (V : P → Submodule ℂ E) : Tw.sub s (⨆ c, V c) = ⨆ c, Tw.sub s (V c) := by
  by_cases hP : P
  · rw [iSup_pos hP, iSup_pos hP]
  · rw [iSup_neg hP, iSup_neg hP]
    rfl

theorem eigSum_tw {I : Type} (h : I → Module.End ℂ E) (Q : (I → ℂ) → Prop) :
    eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (eigSum h fun x => Q fun i => cj s (x i)) := by
  unfold eigSum
  rw [sub_iSup]
  simp only [sub_iSup_prop, eigAt_tw]
  have hcc : ∀ y : I → ℂ, (fun i => cj s (cj s (y i))) = y := fun y => funext fun i => cj_cj s (y i)
  refine le_antisymm (iSup₂_le fun y hy => le_iSup₂_of_le (fun i => cj s (y i)) (by rw [hcc]; exact hy) le_rfl)
    (iSup₂_le fun x hx => le_iSup₂_of_le (fun i => cj s (x i)) hx ?_)
  rw [hcc]

end TwEig

section Concrete

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}

def twE (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    Module.End ℂ ((R.toCx3 F).W j) :=
  (Tw.map (twAt D.what₂.embLL A3.A.v0) H : Module.End ℂ (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H))

theorem theta_jL (j : Fin D.R.m) (t : T) (y : (A3.A.fam.L j t).S.Forms) :
    (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t y) =
      (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (R.jV j t y)) :
        Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) := rfl

theorem twE_smul (j : Fin D.R.m) (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H) (c : ℂ) (v : (R.HW j (sg0 D A3.A)).H) :
    twE R F j H (c • Tw.mk (twAt D.what₂.embLL A3.A.v0) v : Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) =
      (c • Tw.mk (twAt D.what₂.embLL A3.A.v0) (H v) : Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) :=
  (Tw.map (twAt D.what₂.embLL A3.A.v0) H).map_smul c _

theorem intw_of_rat (hM : R.toRealDat.IsModels) (j : Fin D.R.m) (t : T) (i : (A3.liftI j t).OpIx)
    (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H)
    (h : ∀ f, R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = H (R.thG j t (R.jV j t f)))
    (u : (R.toCx3 F).FLC j t) :
    (R.toCx3 F).θ' j t ((R.toCx3 F).opLC j t (Sum.inl i) u) = twE R F j H ((R.toCx3 F).θ' j t u) := by
  have hK := RealDat3.kFormL_of (F := F) hM
  have key : ((R.toCx3 F).θ' j t) ∘ₗ ((R.toCx3 F).opLC j t (Sum.inl i)) = (twE R F j H) ∘ₗ ((R.toCx3 F).θ' j t) := by
    refine LinearMap.ext_on (hK j t).2 ?_
    rintro _ ⟨k, rfl⟩
    have e1 := CxData.jL_opL (R.toCx3 F) hK j t (Sum.inl i) (CxData.bL (A := A3.fam3.amb3) j t k)
    simp only [LinearMap.comp_apply]
    refine (congrArg ((R.toCx3 F).θ' j t) e1.symm).trans ?_
    refine (theta_jL j t _).trans ?_
    refine Eq.trans ?_ (congrArg (twE R F j H) (theta_jL j t _).symm)
    refine Eq.trans ?_ (twE_smul j H _ _).symm
    exact congrArg (fun v => (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) v :
      Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H)) (h _)
  exact LinearMap.congr_fun key u


abbrev SysC (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (j : Fin D.R.m) (p : A3.fam3.base3.Ix) :
    ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) → Prop :=
  cxSys D.what₂.embLL ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1))

theorem sysL_cj (R : RealDat3 D A3 Ks) (j : Fin D.R.m) (p : A3.fam3.base3.Ix) (x : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) :
    SysL A3 j p (fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i)) ↔ SysC A3 j p x := by
  constructor
  · refine fun h => Exists.elim h fun y hy => ⟨y, hy.1, funext fun i => ?_⟩
    have e : cj (twAt D.what₂.embLL A3.A.v0) (x i) = A3.A.v0.embedding (y i) := congrFun hy.2 i
    rw [R.toRealDat.emb0] at e
    rw [← cj_cj (twAt D.what₂.embLL A3.A.v0) (x i), e, cj_cj]
  · refine fun h => Exists.elim h fun y hy => ⟨y, hy.1, funext fun i => ?_⟩
    have e : x i = D.what₂.embLL (y i) := congrFun hy.2 i
    show cj (twAt D.what₂.embLL A3.A.v0) (x i) = A3.A.v0.embedding (y i)
    rw [R.toRealDat.emb0, e]

def unE (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : Module.End ℂ (Tw s E)) : Module.End ℂ E where
  toFun v := Tw.out (h (Tw.mk s v))
  map_add' x y := (congrArg Tw.out (h.map_add (Tw.mk s x) (Tw.mk s y)))
  map_smul' c v := by
    have e : (Tw.mk s (c • v) : Tw s E) = cj s c • Tw.mk s v := by
      show c • v = cj s (cj s c) • v
      rw [cj_cj]
    show Tw.out (h (Tw.mk s (c • v))) = c • Tw.out (h (Tw.mk s v))
    rw [e, map_smul, Tw.out_smul, cj_cj]

theorem twE_commute (j : Fin D.R.m) (a b : Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    Commute (twE R F j a) (twE R F j b) ↔ Commute a b :=
  ⟨fun h => LinearMap.ext fun v => LinearMap.congr_fun h.eq v, fun h => LinearMap.ext fun v => LinearMap.congr_fun h.eq v⟩

theorem rat_of_intw (hM : R.toRealDat.IsModels) (j : Fin D.R.m) (hph : R.phs j ≠ 0) (t : T) (i : (A3.liftI j t).OpIx)
    (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H)
    (h : ∀ u, (R.toCx3 F).θ' j t ((R.toCx3 F).opLC j t (Sum.inl i) u) = twE R F j H ((R.toCx3 F).θ' j t u))
    (f : (A3.A.fam.L j t).S.Forms) :
    R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = H (R.thG j t (R.jV j t f)) := by
  have hK := RealDat3.kFormL_of (F := F) hM
  have e1 := CxData.jL_opL (R.toCx3 F) hK j t (Sum.inl i) f
  have e2 := (congrArg ((R.toCx3 F).θ' j t) e1).trans (h _)
  have e3 := ((theta_jL (R := R) (F := F) j t _).symm.trans e2).trans
    ((congrArg (twE R F j H) (theta_jL j t f)).trans (twE_smul j H _ _))
  exact smul_right_injective (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) hph e3

structure UntwL (g : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (R.HW j (sg0 D A3.A)).H) : Prop where
  rat : ∀ j t i f, R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = g j t i (R.thG j t (R.jV j t f))
  comm : ∀ j, PairComm (g j A3.A.fam.μ0)
  parts : ∀ j p, R.Wp3 j p = eigSum (g j A3.A.fam.μ0) (SysC A3 j p)

theorem sub_inj (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A B : Submodule ℂ E}
    (h : Tw.sub s A = Tw.sub s B) : A = B :=
  SetLike.ext fun x => SetLike.ext_iff.1 h (Tw.mk s x)

theorem hecke_theta_lift_twisted_model_iff_untwisted (hM : R.toRealDat.IsModels) (hph : ∀ j, R.phs j ≠ 0)
    (g : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    HeckeIntertwiningLifts A3 (R.toCx3 F) (fun j t i => twE R F j (g j t i)) ↔ UntwL (R := R) g := by
  have hp : ∀ j p, eigSum (fun i => twE R F j (g j A3.A.fam.μ0 i)) (SysL A3 j p) =
      Tw.sub (twAt D.what₂.embLL A3.A.v0) (eigSum (g j A3.A.fam.μ0) (SysC A3 j p)) := fun j p => by
    have e := eigSum_tw (s := twAt D.what₂.embLL A3.A.v0) (g j A3.A.fam.μ0) (SysL A3 j p)
    have e' : (fun x : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ => SysL A3 j p fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i)) =
        SysC A3 j p := funext fun x => propext (sysL_cj R j p x)
    rw [e'] at e
    exact e
  constructor
  · intro h
    refine ⟨fun j t i f => rat_of_intw hM j (hph j) t i _ (h.intw j t i) f, fun j i i' => (twE_commute j _ _).1 (h.comm j i i'), fun j p => ?_⟩
    refine sub_inj (twAt D.what₂.embLL A3.A.v0) ?_
    exact (h.parts j p).trans (hp j p)
  · intro h
    refine ⟨fun j t i u => intw_of_rat hM j t i _ (h.rat j t i) u, fun j i i' => (twE_commute j _ _).2 (h.comm j i i'), fun j p => ?_⟩
    refine Eq.trans ?_ (hp j p).symm
    exact congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (h.parts j p)

theorem phs_ne_zero (hC : R.WeakCharacterisation F) (j : Fin D.R.m) : R.phs j ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [(hC.phase j).1]; exact one_ne_zero)

def unW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (h : Module.End ℂ ((R.toCx3 F).W j)) :
    Module.End ℂ (R.HW j (sg0 D A3.A)).H :=
  unE (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) h

theorem untw_of_hH (hC : R.WeakCharacterisation F) {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ ((R.toCx3 F).W j)}
    (hH : HeckeIntertwiningLifts A3 (R.toCx3 F) hW) : UntwL (R := R) fun j t i => unW R F j (hW j t i) :=
  (hecke_theta_lift_twisted_model_iff_untwisted (F := F) hC.base.models (phs_ne_zero hC) fun j t i => unW R F j (hW j t i)).1 hH

end Concrete

end GlobalTheory.HeckeLifts₂

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwU

variable {p : ℕ} [Fact p.Prime]

theorem pow_card_sub_dvd {n : ℕ} {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (hirr : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n) (x : W) :
    (p : W) ∣ x ^ (p ^ n) - x := by
  haveI : (Ideal.span {(p : W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
  haveI : Finite (W ⧸ Ideal.span {(p : W)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  letI := Fintype.ofFinite (W ⧸ Ideal.span {(p : W)})
  have h := FiniteField.pow_card (Ideal.Quotient.mk (Ideal.span {(p : W)}) x)
  rw [← Nat.card_eq_fintype_card, hcard, ← map_pow, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  exact h

theorem sigW_sub_pow_dvd (y : Formalism.L2.G.Pend.WW p) : (p : Formalism.L2.G.Pend.WW p) ∣ Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p := by
  have h0 : WittVector.constantCoeff (Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p) = 0 := by
    rw [map_sub, map_pow]
    show (WittVector.frobenius y).coeff 0 - y.coeff 0 ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  have hnu : ¬ IsUnit (Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p) := fun hu => by
    have := hu.map (WittVector.constantCoeff (p := p) (R := Formalism.L2.G.Pend.kb p))
    rw [h0] at this
    exact not_isUnit_zero this
  have hm := (IsLocalRing.mem_maximalIdeal _).2 hnu
  rwa [(WittVector.irreducible p (k := Formalism.L2.G.Pend.kb p)).maximalIdeal_eq, Ideal.mem_span_singleton] at hm

abbrev sigRes (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) : G.P.W v →+* G.P.W v :=
  haveI := (G.P.setting v).frac_alt
  PI.WittUnramWork.sigW (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (G.P.σ v) (G.P.setting v).frob

theorem sigRes_spec (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (x : G.P.W v) :
    algebraMap (G.P.W v) (G.P.Qq v) (sigRes G v x) = G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x) :=
  haveI := (G.P.setting v).frac_alt
  PI.WittUnramWork.sigW_spec _ _ _ x

theorem sigRes_pow (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (s : ℕ) (x : G.P.W v) :
    (G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) x) = algebraMap (G.P.W v) (G.P.Qq v) ((sigRes G v)^[s] x) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ]
    show (G.P.σ v ^ s) (G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x)) = _
    rw [← sigRes_spec, ih, ← Function.iterate_succ_apply]

theorem map_sigRes (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (r : G.P.W v →+* Formalism.L2.G.Pend.WW p) (x : G.P.W v) :
    r (sigRes G v x) = Formalism.MainNotions.FormalGroupSystem.sigW p (r x) := by
  have hS := G.P.setting v
  have hq : ∀ x : G.P.W v, (p : G.P.W v) ∣ x ^ (p ^ G.P.n' v) - x := pow_card_sub_dvd hS.p_unif hS.res_card
  have h := GlobalTheory.T.ringHom_witt_algClosure_eq_of_congr_mod_prime p (G.P.n' v) (G.P.W v) (by have := hS.two_le; omega) hq (r.comp (sigRes G v)) ((Formalism.MainNotions.FormalGroupSystem.sigW p).comp r)
    (fun y => by
      obtain ⟨z, hz⟩ := haveI := hS.frac_alt
        PI.WittUnramWork.sigW_lift (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (G.P.σ v) hS.frob y
      obtain ⟨c, hc⟩ := sigW_sub_pow_dvd (r y)
      refine ⟨r z - c, ?_⟩
      simp only [RingHom.comp_apply]
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast]
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      ring)
  exact congrArg (fun f => f x) h

theorem nonempty_cEmbC : ∀ (p : ℕ) [Fact p.Prime] (G : GAtP p), 0 < G.P.nV → Nonempty (CEmbC G) := by
  intro p _ G hV
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_coefficient_field_embedding_padic_complex p G hV
  let φ : ∀ v, G.P.W v →+* ℂ_[p] := fun v => (E.iK.comp (G.P.ι v)).comp (algebraMap (G.P.W v) (G.P.Qq v))
  have hφ1 : ∀ v x, ‖φ v x‖ ≤ 1 := fun v x => by
    show ‖E.iK (G.P.ι v (algebraMap _ _ x))‖ ≤ 1
    rw [(G.P.setting v).ι_comp]
    exact E.int _
  have hφr : ∀ v x, φ v x ∈ (Formalism.L2.G.Pend.wToC p).range := fun v x => by
    have hS := G.P.setting v
    exact GlobalTheory.T.mem_range_witt_algClosure_of_bounded_ringHom p (G.P.n' v) (G.P.W v) (by have := hS.two_le; omega) (pow_card_sub_dvd hS.p_unif hS.res_card)
      hS.eq_sum_herm_smul_frame_of_inW (φ v) (hφ1 v) x
  let eW : Formalism.L2.G.Pend.WW p ≃+* (Formalism.L2.G.Pend.wToC p).range :=
    RingEquiv.ofBijective (Formalism.L2.G.Pend.wToC p).rangeRestrict
      ⟨fun a b h => Formalism.L2.G.Pend.wToC_injective p (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let rd : ∀ v, G.P.W v →+* Formalism.L2.G.Pend.WW p := fun v =>
    eW.symm.toRingHom.comp ((φ v).codRestrict (Formalism.L2.G.Pend.wToC p).range (hφr v))
  have hrd : ∀ v x, Formalism.L2.G.Pend.wToC p (rd v x) = φ v x := fun v x => by
    have := congrArg Subtype.val (eW.apply_symm_apply ((φ v).codRestrict (Formalism.L2.G.Pend.wToC p).range (hφr v) x))
    exact this
  refine ⟨⟨E, rd, ?_⟩⟩
  intro v s x
  have hit : ∀ y, rd v ((sigRes G v)^[s] y) = (Formalism.MainNotions.FormalGroupSystem.sigW p)^[s] (rd v y) := by
    induction s with
    | zero => intro y; rfl
    | succ s ih => intro y; rw [Function.iterate_succ_apply, ih, map_sigRes, ← Function.iterate_succ_apply]
  rw [sigRes_pow, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, ← hit, hrd]
  rfl

end GlobalTheory.TwU
end
end
