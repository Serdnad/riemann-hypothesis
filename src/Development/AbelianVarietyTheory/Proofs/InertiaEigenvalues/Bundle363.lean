module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle349
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.Per.FontaineBound

theorem linearIndepOn_of_invariant {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W) (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * a g b' = a g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn B v s := by
  first
  | (rename_i h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13; revert K B W G ι h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 a σ hσ hreg v hv s h; exact @_root_.GlobalTheory.SimpStatement.main)
  | exact @_root_.GlobalTheory.SimpStatement.main
  | exact _root_.GlobalTheory.SimpStatement.main
  | (apply _root_.GlobalTheory.SimpStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SimpStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SimpStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SimpStatement.main ..)

section General

variable {G Qp K B LL V : Type} [Group G] [Field Qp] [Field K] [Algebra Qp K] [CommRing B] [IsDomain B]
  [Algebra Qp B] [Algebra K B] [IsScalarTower Qp K B] [Field LL] [Algebra Qp LL]
  [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def invs (act : G →* (B ≃ₐ[K] B)) (ρ : Representation LL G V) : Submodule LL (V ⊗[Qp] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
    (((act g).toAlgHom.toLinearMap).restrictScalars Qp) - LinearMap.id)

theorem finite_finrank_le_base [FiniteDimensional Qp K] [FiniteDimensional Qp V] (act : G →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (ρ : Representation LL G V) :
    Module.Finite Qp (invs (Qp := Qp) act ρ) ∧
      finrank Qp (invs (Qp := Qp) act ρ) ≤ finrank Qp K * finrank Qp V := by
  let σ : G → B ⊗[Qp] V →ₗ[Qp] B ⊗[Qp] V := fun g =>
    TensorProduct.map (((act g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : B) w, σ g (b • w) = act g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  let U : Submodule K (B ⊗[Qp] V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add (f := _), hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul B c x, hσ, hx g, AlgEquiv.commutes] }
  have hr : Module.rank K U ≤ finrank Qp V := by
    refine rank_le fun s hs => ?_
    have h1 : LinearIndepOn K (fun x : U => (x : B ⊗[Qp] V)) s := hs.map' U.subtype U.ker_subtype
    have h2 := linearIndepOn_of_invariant (fun g b => act g b) (fun g => (σ g).toAddMonoidHom) hσ hreg
      (fun x : U => (x : B ⊗[Qp] V)) (fun g x => x.2 g) s h1
    simpa using LinearIndependent.fintype_card_le_finrank h2
  haveI : Module.Finite K U := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0
  have hr' : finrank K U ≤ finrank Qp V := finrank_le_of_rank_le hr
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V B x) =
      TensorProduct.comm Qp V B (AlgebraTensorModule.map (ρ g)
        (((act g).toAlgHom.toLinearMap).restrictScalars Qp) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let f : invs (Qp := Qp) act ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V B x, fun g => by
        have := x.2
        simp only [invs, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V B) c _) }
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext ((TensorProduct.comm Qp V B).injective (congrArg Subtype.val h))
  refine ⟨Module.Finite.of_injective f hf, (LinearMap.finrank_le_finrank_of_injective hf).trans ?_⟩
  rw [← Module.finrank_mul_finrank Qp K U]
  exact Nat.mul_le_mul_left _ hr'

theorem finite_finrank_le [FiniteDimensional Qp K] [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (act : G →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (ρ : Representation LL G V) :
    Module.Finite LL (invs (Qp := Qp) act ρ) ∧
      finrank LL (invs (Qp := Qp) act ρ) ≤ finrank Qp K * finrank LL V := by
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨h1, h2⟩ := finite_finrank_le_base (Qp := Qp) act hreg ρ
  refine ⟨Module.Finite.of_restrictScalars_finite Qp LL _, ?_⟩
  rw [← Module.finrank_mul_finrank Qp LL (invs (Qp := Qp) act ρ), ← Module.finrank_mul_finrank Qp LL V,
    mul_left_comm] at h2
  exact Nat.le_of_mul_le_mul_left h2 Module.finrank_pos

end General

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem frac_dR (hF : IsField BdR) (b b' : BdR) (hb : b ≠ 0)
    (h : ∀ g, b * PD.actdR g b' = PD.actdR g b * b') : ∃ c : K, b' = algebraMap K BdR c * b := by
  letI : Field BdR := hF.toField
  obtain ⟨c, hc⟩ := PD.invdR (b' / b) fun g => by
    have hg : PD.actdR g b ≠ 0 := (map_ne_zero _).2 hb
    rw [map_div₀, div_eq_div_iff hg hb, mul_comm, h g, mul_comm]
  exact ⟨c, by rw [hc, div_mul_cancel₀ _ hb]⟩


include PD in
theorem isDomain_cris (hF : IsField BdR) : IsDomain B :=
  letI : Field BdR := hF.toField
  PD.ι_inj.isDomain PD.ι.toRingHom

variable {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]

theorem ddR_finite_le (hF : IsField BdR) (ρ : Representation LL G V) :
    Module.Finite LL (DdR PD ρ) ∧ finrank LL (DdR PD ρ) ≤ finrank Qp K * finrank LL V := by
  haveI := hF.isDomain
  haveI := PD.finK
  exact finite_finrank_le PD.actdR (frac_dR PD hF) ρ

end Periods

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}

theorem isField_of_tied (T : LocTied l P AI) : IsField P.R.BdR :=
  T.eD.toMulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1

theorem frac_cris (hfit : GlobalTheory.MemLoc.Fits T C) (hinj : C.TensorInj) (K : FinExt l) (b b' : P.R.B) (hb : b ≠ 0)
    (h : ∀ g, b * (P.PD K).actB g b' = (P.PD K).actB g b * b') :
    ∃ c : ↥(K0 K), b' = algebraMap ↥(K0 K) P.R.B c * b := by
  have hF : IsField P.R.BdR := isField_of_tied T
  obtain ⟨c, hc⟩ := frac_dR (P.PD K) hF ((P.PD K).ι b) ((P.PD K).ι b')
    (fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm)))
    (fun g => by rw [← (P.PD K).ι_comm, ← (P.PD K).ι_comm, ← map_mul, ← map_mul, h g])
  have hcU : (c : Om l) ∈ MaximalUnramifiedExtension l := by
    by_contra hn
    have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) ![(1 : Om l), (c : Om l)] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro a ha
      apply hn
      rw [← ha, Algebra.smul_def, mul_one]
      exact a.2
    have h0 := hinj 2 _ hli ![T.eB b', - T.eB b] (by
      have h1 := congrArg T.eD hc
      rw [map_mul, P.PD_ι, P.PD_ι, hfit.ι, hfit.ι] at h1
      have h2 : T.eD (algebraMap ↥K.1 P.R.BdR c) = C.oD (c : Om l) := hfit.o _
      rw [h2] at h1
      simp [Fin.sum_univ_two, h1]) 1
    apply hb
    apply T.eB.injective
    simpa using h0
  refine ⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩
  rw [map_mul, AlgHom.commutes, hc]
  rfl

theorem dcris_finite_le (hfit : GlobalTheory.MemLoc.Fits T C) (hinj : C.TensorInj) (K LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  haveI := isDomain_cris (P.PD K) (isField_of_tied T)
  haveI := (P.PD K).finK₀
  haveI := LL.2
  exact finite_finrank_le (P.PD K).actB (frac_cris hfit hinj K) ρ

end Tied

end GlobalTheory.Per.FontaineBound
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

theorem isSubFam_of_isSubSumOf {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL))
    (W A A' : GRep G Qp LL O) (hW : BlochKatoDuality.IsSubSumOf W.ρ A.ρ A'.ρ) (hA : IsSubFam Ms A)
    (hA' : IsSubFam Ms A') : IsSubFam Ms W := by
  obtain ⟨a, b, p, q, hp, hq, hinj⟩ := hW
  obtain ⟨a₁, x₁, p₁, hp₁, hinj₁⟩ := hA
  obtain ⟨a₂, x₂, p₂, hp₂, hinj₂⟩ := hA'
  let e : Fin (a * a₁ + b * a₂) ≃ (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  let X : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → ι :=
    Sum.elim (fun ij => x₁ ij.2) (fun ij => x₂ ij.2)
  let P : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → W.V →ₗ[LL] (Fin k → LL) :=
    Sum.elim (fun ij => (p₁ ij.2).comp (p ij.1)) (fun ij => (p₂ ij.2).comp (q ij.1))
  refine ⟨a * a₁ + b * a₂, X ∘ e, P ∘ e, ?_, ?_⟩
  · intro j g v
    simp only [Function.comp]
    generalize e j = s
    rcases s with ⟨i, j'⟩ | ⟨i, j'⟩
    · simp only [P, X, Sum.elim_inl, LinearMap.comp_apply, hp, hp₁]
    · simp only [P, X, Sum.elim_inr, LinearMap.comp_apply, hq, hp₂]
  · intro v hv
    apply hinj v
    · intro i
      apply hinj₁
      intro j'
      have h := hv (e.symm (Sum.inl (i, j')))
      simpa [P] using h
    · intro i
      apply hinj₂
      intro j'
      have h := hv (e.symm (Sum.inr (i, j')))
      simpa [P] using h

end Gen

section OnePD

theorem liftAll_of_liftFam :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ ι k Ms e A A' hL hA hA'
  intro W₁ W₂ h₁ h₂ L₁ L₂ F hF
  exact hL W₁ W₂ (isSubFam_of_isSubSumOf Ms W₁ A A' h₁ hA hA')
    (isSubFam_of_isSubSumOf Ms W₂ A A' h₂ hA hA') L₁ L₂ F hF

end OnePD

end GlobalTheory.Pass.LocDual

end
end

section

noncomputable section

namespace GlobalTheory.HfCharProof

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem act_chiRat (c : ℕ) (g : Br.G D.nbr i w hw) (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x =
      (D.nbr i w hw).toLL (((chiU D.nd i c * (chiU D.nd i 1)⁻¹)
        (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) • x := by
  funext b
  rw [Subsingleton.elim b 0]
  change (Br.loc D.nbr i w hw (chiRatO D.nd i c) g).mulVec x 0 = _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
  congr 1
  change (D.nbr i w hw).toLL (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0) = _
  congr 1
  simp [chiRatO, twistM]

theorem cont_chiRat (c : ℕ) (x : Fin 1 → Br.LL D.nbr i w hw) :
    Continuous fun g => matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x := by
  simp only [act_chiRat]
  have hs : Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  have hL : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => (D.nbr i w hw).toLL
      ((D.nd.chi i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      (D.nbr i w hw).toLL
      ((D.nd.chi i 1 (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) : (D.nd.O i)ˣ) : D.nd.O i) :=
    (hL.comp ((D.nd.chi_cont i c).comp hs)).mul
      (hL.comp ((D.nd.chi_cont i 1).comp (hs.comp continuous_inv)))
  refine Continuous.smul (h1.congr fun g => ?_) continuous_const
  rw [← map_mul, ← Units.val_mul, map_inv, map_inv, map_inv]
  rfl

theorem chiRat_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Formalism.MainNotions.N.GE D.nd) :
    (chiU D.nd i (n + 1) * (chiU D.nd i 1)⁻¹) g = (epsU D.nd i g)⁻¹ ^ n := by
  rcases hn with rfl | hc
  · simp
  · have h := D.nd.chi_def i (n + 1) (by omega) hc
    change D.nd.chi i (n + 1) g * (D.nd.chi i 1)⁻¹ g = _
    rw [mul_comm, h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl

theorem eps_eq (g : Br.G D.nbr i w hw) :
    (D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  rw [Br.PD, (D.loc _).PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
  exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)

theorem act_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Br.G D.nbr i w hw)
    (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i (n + 1))) g x =
      ((algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹) ^ n • x := by
  rw [act_chiRat, chiRat_eq D i n hn, Units.val_pow_eq_pow_val, map_pow, map_units_inv, eps_eq]

def chiLat (c : ℕ) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) where
  V := Fin 1 → Br.LL D.nbr i w hw
  ρ := matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c))
  cont := cont_chiRat D i w hw c
  L := Br.locLat D.nbr i w hw (chiRatO D.nd i c)




theorem hfChar : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LocalSituation.Conclusion4 D HW F → InertEq D →
    ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      D.nd.l i ≠ 2 → (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 → HfChar i w hw := by
  intro D HW F h4 hI i w hw h2 hK
  have hs := (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 hK
  have hT := (h4 (D.nd.l i) _ 1 _ hs).2
  have hr : ∀ c, finrank (Br.LL D.nbr i w hw) (chiLat D i w hw c).V = 1 := fun c =>
    Module.finrank_fin_fun _
  refine ⟨fun c hc => ?_, fun f hf => ?_⟩
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    exact ((hT n (chiLat D i w hw (n + 1)) (hr _) (act_eq D i w hw n (Or.inr hc2))).2.1 (by omega)).le
  · obtain ⟨-, x, hx⟩ :=
      ((hT 0 (chiLat D i w hw 1) (hr _) (act_eq D i w hw 0 (Or.inl rfl))).2.2 rfl f).1 hf
    refine ⟨x, fun g hg => hx g ?_⟩
    rw [hI i w hw] at hg
    exact hg

end GlobalTheory.HfCharProof

end
end

section

noncomputable section

namespace GlobalTheory.TopSteps.FinSummandJumps

open Module

theorem finsum_count_neg (U : Multiset ℤ) (m : ℤ → ℤ) (h : ∀ a, m a = (U.count a : ℤ)) :
    ∑ᶠ (a : ℤ) (_ : a < 0), m a = (Multiset.card (U.filter (· < 0)) : ℤ) := by
  classical
  have h1 : ∀ a : ℤ, ∑ᶠ (_ : a < 0), m a = (((U.filter (· < 0)).count a : ℕ) : ℤ) := fun a => by
    rw [finsum_eq_if, h, Multiset.count_filter]
    split_ifs <;> simp
  rw [finsum_congr h1, finsum_eq_sum_of_support_subset (s := (U.filter (· < 0)).toFinset),
    ← Nat.cast_sum, Multiset.toFinset_sum_count_eq]
  intro a ha
  have ha' : (U.filter (· < 0)).count a ≠ 0 := fun h0 => ha (by simp only [h0, Nat.cast_zero])
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 ha'))

section General

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

theorem finsum_multV_neg {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (U : ZMod n → Multiset ℤ)
    (hU : ∀ i, HasJumps PD ρ (emb i) (U i)) :
    ∑ᶠ (τ : K →ₐ[Qp] LL), ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      ∑ i, (Multiset.card ((U i).filter (· < 0)) : ℤ) := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  let e : ZMod n ≃ (K →ₐ[Qp] LL) := (Equiv.ofBijective emb hemb).trans (E.arrowCongr AlgEquiv.refl)
  have he : ∀ i x, e i (algebraMap K₀ K x) = emb i x := fun i x => by
    change emb i (E.symm (E x)) = emb i x
    rw [AlgEquiv.symm_apply_apply]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => finsum_count_neg (U i) _ (hU i (e i) (he i))

end General


open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.TopSteps.FinSummandDim in
theorem fSummand : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), tableLineDegreeTwo.BlochKatoJumpDimension (P.PD S.K) (LL := ↥S.LL.1) (O := S.O) (IK S.K) → S.CrysCalc → S.Vanish → S.FreeH → S.FSummand := by
  intro l _ P S hB hC hV hH
  obtain ⟨⟨-, -, -, hemb, -⟩, -⟩ := S.hyp
  have : IsTopologicalAddGroup (tw S hC).V := IsModuleTopology.topologicalAddGroup ↥S.LL.1 (tw S hC).V
  have h := hB.1 (tw S hC).V (tw S hC).ρ (tw S hC).cont (tw_crysWith S hC).1
  exact fSummand_of_dim S hC hV hH (h.trans (congrArg _
    (finsum_multV_neg (P.PD S.K) S.emb hemb (bijective_maxUnramifiedSubfield_algebraMap S) _ (tw_crysWith S hC).2)))

end GlobalTheory.TopSteps.FinSummandJumps
end
end

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsIrr ψ → ∀ θ : (ZMod g)ˣ →* ℂˣ,
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0) ∧
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc 1 n (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0) := by
  first | exact @GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv | exact GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv | (intros; apply GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv <;> assumption)
end
