module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle750
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle028
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle752
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianEqIffSiegelParabolicCoset
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle751
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

theorem ratMul_ratMul {m : ℕ} {a c : ℕ} (c₁ : Matrix (Fin a) (Fin m) D.host.E) (c₂ : Matrix (Fin m) (Fin m) D.host.E)
    (u : Mx D m c) : ratMul c₁ (ratMul c₂ u) = ratMul (c₁ * c₂) u := by
  unfold ratMul
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem covolOne_integral_ratMul {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (c c' : Matrix (Fin m) (Fin m) D.host.E) (h1 : c' * c = 1)
    (h2 : c * c' = 1) (φ : Mx D m n → ℂ) (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (ratMul c a) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hl : ∀ a : Mx D m n, ratMul c' (ratMul c a) = a := fun a => by
    rw [ratMul_ratMul, h1, ratMul_one]
  have hr : ∀ a : Mx D m n, ratMul c (ratMul c' a) = a := fun a => by
    rw [ratMul_ratMul, h2, ratMul_one]
  have mem : ∀ (d : Matrix (Fin m) (Fin m) D.host.E) (g : GlobalTheory.MixModel.ratMx D m n),
      ratMul d (g : Mx D m n) ∈ GlobalTheory.MixModel.ratMx D m n := fun d g =>
    GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem d) g.2
  let A : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => ratMul c a
      invFun := fun a => ratMul c' a
      left_inv := hl
      right_inv := hr
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  let L : Mx D m n ≃ₜ+ Mx D m n :=
    { A with
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  let e : Mx D m n ≃ᵐ Mx D m n := L.toHomeomorph.toMeasurableEquiv
  haveI := hμ.1
  have hH : (μ.map e).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving e μ (μ.map e) := e.measurable.measurePreserving μ
  let r : GlobalTheory.MixModel.ratMx D m n ≃ GlobalTheory.MixModel.ratMx D m n :=
    { toFun := fun g => ⟨ratMul c' (g : Mx D m n), mem c' g⟩
      invFun := fun g => ⟨ratMul c (g : Mx D m n), mem c g⟩
      left_inv := fun g => Subtype.ext (hr _)
      right_inv := fun g => Subtype.ext (hl _) }
  have hcov : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) (μ.map e) (e '' 𝓕) := by
    refine ⟨hH, ?_, ?_⟩
    · refine hμ.2.1.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving r fun g a => ?_
      show ratMul c (ratMul c' (g : Mx D m n) + a) = (g : Mx D m n) + ratMul c a
      unfold ratMul
      rw [Matrix.mul_add]
      congr 1
      exact hr _
    · rw [e.map_apply, e.preimage_image]; exact hμ.2.2
  have h := GlobalTheory.MixModel.covolOne_integral_eq hμ hcov φ hφ
  rw [setIntegral_map_equiv, e.preimage_image] at h
  exact h

theorem exists_frame_change {W : HSp D} {Y : Lag W}
    {C C' : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hC : IsLagFrame W Y C) (hC' : IsLagFrame W Y C') :
    ∃ c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E,
      C'.1 = C.1 * c ∧ C'.2 = C.2 * c ∧ c * c' = 1 ∧ c' * c = 1 := by
  have mem : ∀ {C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E},
      IsLagFrame W Y C → ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 :=
    fun h j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  let v : ∀ C, IsLagFrame W Y C → Fin W.rank → Y.1 := fun C h j => ⟨_, mem h j⟩
  have sp : ∀ C (h : IsLagFrame W Y C), ⊤ ≤ Submodule.span D.host.E (Set.range (v C h)) := by
    intro C h
    refine le_of_eq (Submodule.map_injective_of_injective Y.1.injective_subtype ?_).symm
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact h
  have li : ∀ C (h : IsLagFrame W Y C), LinearIndependent D.host.E (v C h) := fun C h =>
    linearIndependent_of_top_le_span_of_card_eq_finrank (sp C h) (by rw [Fintype.card_fin, Y.2.1])
  let b := Module.Basis.mk (li C hC) (sp C hC)
  let b' := Module.Basis.mk (li C' hC') (sp C' hC')
  have hb : ∀ j, (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C.1 a j), (fun a => C.2 a j)) :=
    fun j => by simp [b, v]
  have hb' : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C'.1 a j), (fun a => C'.2 a j)) :=
    fun j => by simp [b', v]
  have key : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
      ∑ i, b.toMatrix b' i j • (b i : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) := fun j => by
    have := congrArg Subtype.val (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [Module.Basis.toMatrix_apply]
    exact this.symm
  refine ⟨b.toMatrix b', b'.toMatrix b, ?_, ?_, Module.Basis.toMatrix_mul_toMatrix_flip b b', Module.Basis.toMatrix_mul_toMatrix_flip b' b⟩
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.1 a) (key j)
    simp only [hb, hb', Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.2 a) (key j)
    simp only [hb, hb', Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lagTerm_frame_indep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (Y : Lag W) C C', IsLagFrame W Y C → IsLagFrame W Y C' → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C' f₁ f₂ := by
  intro D ψ V W μ 𝓕 hμ hψ f₁ f₂ h₁ h₂ Y C C' hC hC'
  obtain ⟨c, c', e1, e2, hcc, hc'c⟩ := exists_frame_change hC hC'
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  unfold lagTerm
  rw [e1, e2]
  simp only [← ratMul_ratMul]
  refine (covolOne_integral_ratMul (m := W.rank) (n := V.rank) hμ c c' hc'c hcc
    (fun u => f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) ?_).symm
  rintro _ ⟨γ, rfl⟩ a
  exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC h₁ h₂ γ a

end GlobalTheory.RawLift

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ChosenPrimes

namespace GlobalTheory.NewPrimePick

theorem exists_newPlace : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → n < R → ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host)), AdmFam X i M H S d → L ≤ H → ∀ (U : Subgroup (GE N)) (h : GE N), IsOpen (U : Set (GE N)) → U.Normal → U ≤ L → h ∈ L → (∀ b : Fin R, b.val < n → d (P (.inl b)) h = 1) → (∀ b : Fin R, n ≤ b.val → Ine (F := D.host.E) (N.plOm.1 (P (.inl b))) ≤ U) → ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A₀ L z P' ∧ ∃ σ γ g : GE N, NewPl i M L (P' (.inr (Fin.last n))) (d (P' (.inr (Fin.last n)))) σ γ ∧ d (P' (.inr (Fin.last n))) σ = 1 ∧ g * σ * g⁻¹ * h⁻¹ ∈ U := by
  intro hC D N X i s M R n d A L z P _ _ hsm hst _ H S hA hLH U h hU hUn hUL hh hh1 hIU
  classical
  obtain ⟨-, -, -, hd⟩ := hA
  obtain ⟨⟨hL, hLn, -⟩, hLr, -⟩ := hsm
  obtain ⟨⟨ha1, ha2, ha3⟩, hs1, hs2⟩ := hst
  have hl := (X.lPrime i).out
  set m := 2 * X.l i ^ M with hm
  have hn1 : 1 < m := by have := Nat.pow_pos (n := M) hl.pos; omega
  have hn0 : m ≠ 0 := by omega
  have hval := exists_values (U ⊓ ⨅ b : {b : Fin R // b.val < n}, (d (P (.inl b.1))).ker)
    (fun b : {b : Fin R // n ≤ b.val} => d (P (.inl b.1))) (fun b c => by
      obtain ⟨γ, hγ, e⟩ := (ha3 (.inl b.1)).2.2.2.2 _ (over_refl _) _ (N.plOm.2 (P (.inl b.1))) c
      have key : ∀ b' : Fin R, b' ≠ b.1 → d (P (.inl b')) γ = 1 := fun b' hb' =>
        (ha3 (.inl b')).2.2.2.1 _ (fun h => hb' (Sum.inl_injective (ha2 _ _ h))) _ (N.plOm.2 (P (.inl b.1))) γ hγ
      refine ⟨γ, ⟨hIU b.1 b.2 hγ, Subgroup.mem_iInf.2 fun b' => key b'.1 fun h => ?_⟩, e,
        fun b' hb' => key b'.1 fun h => hb' (Subtype.ext h)⟩
      have h1 := b'.2
      have h2 := b.2
      rw [h] at h1
      omega)
  obtain ⟨γ₀, hγ₀, hγd⟩ := hval fun b =>
    Multiplicative.ofAdd (if n = b.1.val then 1 else 0) * (d (P (.inl b.1)) h)⁻¹
  have hγh : ∀ b : Fin R, d (P (.inl b)) (γ₀ * h) = Multiplicative.ofAdd (if n = b.val then 1 else 0) := by
    intro b
    rw [map_mul]
    rcases lt_or_ge b.val n with hb | hb
    · have h1 : d (P (.inl b)) γ₀ = 1 := Subgroup.mem_iInf.1 hγ₀.2 ⟨b, hb⟩
      rw [h1, hh1 b hb, if_neg (by omega), mul_one]
      rfl
    · rw [hγd ⟨b, hb⟩, inv_mul_cancel_right]
  let V : Subgroup (GE N) := U ⊓ ⨅ b, (d (P (.inl b))).ker
  have hV : IsOpen (V : Set (GE N)) := by
    refine hU.inter ?_
    show IsOpen ((⨅ b, (d (P (.inl b))).ker : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun b => (ha3 (.inl b)).1
  have hVn : V.Normal := by
    have : (⨅ b, (d (P (.inl b))).ker).Normal := Subgroup.normal_iInf_normal fun b => inferInstance
    infer_instance
  obtain ⟨T₀, hT₀, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split D.host
  let T : Set (PlE D.host) := ((↑A ∪ ↑S ∪ ↑(X.S0 i)) ∪ (T₀ ∪ {P | P.asIdeal.ramificationIdx ℤ ≠ 1}) ∪
    ({v | ((m : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} ∪
      {v | ∃ B : ValuationSubring N.Om, IsPlaceOver B v ∧ ¬ Ine (F := D.host.E) B ≤ U})) ∪ Set.range P
  have hT : T.Finite :=
    ((((A.finite_toSet.union S.finite_toSet).union (X.S0 i).finite_toSet).union
      (hT₀.union (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified D.host.E).2)).union
      ((finite_mem hn0).union (finite_ram hU))).union (Set.finite_range P)
  obtain ⟨p, hp⟩ := exists_pick hC hV hVn (γ₀ * h) hT
  have h1 : ∀ v, Over p v → ((((v ∉ A ∧ v ∉ S) ∧ v ∉ X.S0 i) ∧ v ∉ T₀ ∧ v.asIdeal.ramificationIdx ℤ = 1) ∧
      ((m : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧ v ∉ Set.range P := fun v hv => by
    have : v ∉ T := (hp.1 v hv).1
    simpa only [T, Set.mem_union, not_or, Finset.mem_coe, Set.mem_ofPred_eq, not_exists, not_and, not_not] using this
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 p)
  obtain ⟨k, hk⟩ := hp.2 σ hσ
  have hσL : σ ∈ L := by
    have h2 := hLn.conj_mem _ (L.mul_mem (hUL hk.1) (L.mul_mem (hUL hγ₀.1) hh)) k⁻¹
    have e : k⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹ * (γ₀ * h)) * k⁻¹⁻¹ = σ := by group
    rwa [e] at h2
  have hP0 := h1 p (over_refl p)
  have hq := norm_mod (N.plOm.2 p) hn1 hP0.1.2.1 hσ (hLr σ hσL)
  have hIp : Ine (F := D.host.E) (N.plOm.1 p) ≤ U := hP0.1.2.2 _ (N.plOm.2 p)
  have hdec : DecV N p ≤ L := dec_le (N.plOm.2 p) hL (hIp.trans hUL) hσ hσL
  have hspl : IsSplitPl D.host p := hsp p hP0.1.1.2.1 (hp.1 p (over_refl p)).2
  have hgood : GoodChar X i M p (d p) := hd p hP0.1.1.1.1.2 hspl (hdec.trans hLH)
  have haux : ∀ v, Over p v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % m = 1 := by
    refine fun v hv => ⟨hsp v (h1 v hv).1.1.2.1 (hp.1 v hv).2, (hp.1 v hv).2, (h1 v hv).1.1.2.2, (h1 v hv).1.1.1.2,
      (h1 v hv).1.1.1.1.1, ?_⟩
    rcases hv with rfl | hv
    · exact hq
    · rwa [normV_conj hv]
  let P' : Fin R ⊕ Fin (n + 1) → PlE D.host :=
    Sum.elim (fun a => P (.inl a)) (Fin.snoc (α := fun _ => PlE D.host) (fun a => P (.inr a)) p)
  have e1 : P' (.inr (Fin.last n)) = p := by simp [P']
  have e2 : ∀ q, P' (Sum.map id Fin.castSucc q) = P q := by
    rintro (a | a) <;> simp [P']
  have cases : ∀ q : Fin R ⊕ Fin (n + 1), q = .inr (Fin.last n) ∨ ∃ q₀, q = Sum.map id Fin.castSucc q₀ := by
    rintro (a | a)
    · exact Or.inr ⟨.inl a, rfl⟩
    · refine Fin.lastCases (Or.inl rfl) (fun a => Or.inr ⟨.inr a, rfl⟩) a
  refine ⟨P', e2, ⟨⟨fun q => ?_, fun q q' => ?_, fun q => ?_⟩, hs1, fun a => ?_⟩, ?_⟩
  · rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact haux
    · rw [e2]; exact ha1 q
  · rcases cases q with rfl | ⟨q, rfl⟩ <;> rcases cases q' with rfl | ⟨q', rfl⟩
    · exact fun _ => rfl
    · rw [e1, e2]; exact fun h => ((h1 _ h).2 ⟨q', rfl⟩).elim
    · rw [e1, e2]; exact fun h => ((h1 _ (over_symm h)).2 ⟨q, rfl⟩).elim
    · rw [e2, e2]; exact fun h => by rw [ha2 _ _ h]
  · show GoodChar X i M (P' q) (d (P' q))
    rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact hgood
    · rw [e2]; exact ha3 q
  · refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [e1]
      refine ⟨hdec, fun b τ hτ => ?_⟩
      obtain ⟨k', hk'⟩ := hp.2 τ hτ
      have h2 : d (P (.inl b)) _ = 1 := Subgroup.mem_iInf.1 hk'.2 b
      rw [map_mul, map_inv, hγh] at h2
      simp only [map_mul, map_inv, mul_inv_cancel_comm, mul_inv_eq_one] at h2
      exact h2
    · have e3 : P' (.inr a.castSucc) = P (.inr a) := e2 (.inr a)
      rw [e3]
      exact hs2 a
  · rw [e1]
    obtain ⟨γ, hγ, hγ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (Multiplicative.ofAdd 1)
    obtain ⟨τ, hτ, hτ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (d p σ)⁻¹
    refine ⟨σ * τ, γ, k, ⟨fun v hv => (haux v hv).2.2.2.1, hspl, hq, hdec, hgood.1, ?_, hγ, hγ1⟩, ?_, ?_⟩
    · first | exact isFrob_mul_of_mem_Ine hσ hτ | exact isFrob_mul_of_mem_Ine hτ hσ
    · rw [map_mul, hτ1, mul_inv_cancel]
    · have h2 := U.mul_mem (U.mul_mem (hUn.conj_mem _ (hIp hτ) (k * σ)) hk.1) hγ₀.1
      have e : k * σ * τ * (k * σ)⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹) * γ₀ = k * (σ * τ) * k⁻¹ * h⁻¹ := by group
      rwa [e] at h2

end GlobalTheory.NewPrimePick
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.CellDec.lastRow_sub_notMem_latt : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (w : HeightOneSpectrum (𝓞 E)),
      l.1 w (Fin.last m) < 0 →
      (fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∉
        GlobalTheory.ThetaPoisson.latt (m + 1) J := by
  intro E _ _ m T ϖ hϖ J hJ g hg l w hlw hmem
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hwT : w ∉ T := fun h => by rw [l.2 w h] at hlw; simp at hlw
  set a := l.1 w (Fin.last m) with ha
  set K := GlobalTheory.CellDec.compV E (m+1) w k with hKdef
  have hK : K ∈ GlobalTheory.LFun.KGL w (n := (m+1)) := GlobalTheory.CellDec.mem_US.1 hk w hwT
  obtain ⟨-, hK2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have hU := (GlobalTheory.SmGL.mem_unipB _).1 (GlobalTheory.CellDec.compV_mem_unipB w hu)
  have hent : ∀ i, (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
      ((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i := by
    intro i
    have h1 : (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
        (GlobalTheory.CellDec.compV E (m+1) w (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k))).val (Fin.last m) i := rfl
    rw [h1, map_mul, map_mul, GlobalTheory.CellDec.compV_tl, Units.val_mul, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hU.2, one_mul]
    · intro j _ hj
      rw [hU.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hb : ∀ i, Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i -
      (if i = Fin.last m then 1 else 0)) ≤ 1 := by
    intro i
    have h2 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hmem i) w
    rw [hJ w hwT, neg_zero, WithZero.exp_zero] at h2
    convert h2 using 2
    rw [← hent i]
    by_cases hi : i = Fin.last m
    · subst hi; simp
    · simp [hi]
  have hϖv : Valued.v ((ϖ w : w.adicCompletion E)) = WithZero.exp (-1 : ℤ) := hϖ w
  have hrow : ∀ i, Valued.v (K.val (Fin.last m) i) < 1 := by
    intro i
    have hle : Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) ≤ 1 := by
      by_cases hi : i = Fin.last m
      · have := hb i
        rw [if_pos hi] at this
        calc _ = Valued.v ((((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i - 1) + 1) := by
              rw [sub_add_cancel]
          _ ≤ max _ _ := Valuation.map_add _ _ _
          _ ≤ 1 := max_le this (by simp)
      · simpa [hi] using hb i
    have e : K.val (Fin.last m) i = ((ϖ w ^ (-a) : (w.adicCompletion E)ˣ) : w.adicCompletion E) *
        (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) := by
      rw [← mul_assoc, ← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
    rw [e, Valuation.map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖv, ← WithZero.exp_zsmul]
    have hlt : WithZero.exp ((-a) • (-1 : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; simp; omega
    calc _ ≤ WithZero.exp ((-a) • (-1 : ℤ)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  have hone : ∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m) = 1 := by
    have := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) (w.adicCompletion E) => M (Fin.last m) (Fin.last m))
      (Units.mul_inv K)
    simpa [Matrix.mul_apply] using this
  have hlt : Valued.v (∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Valuation.map_mul]
    have hj : Valued.v ((K⁻¹).val j (Fin.last m)) ≤ 1 := hK2 j (Fin.last m)
    calc _ ≤ Valued.v (K.val (Fin.last m) j) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hrow j
  rw [hone, map_one] at hlt
  exact lt_irrefl _ hlt
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.CellDec.DetMod

theorem prod_adl {E : Type} [Field E] [NumberField E] {ι : Type} (s : Finset ι)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : ι → HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    ∏ i ∈ s, GlobalTheory.CellDec.adl ϖ (m i) = GlobalTheory.CellDec.adl ϖ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.CellDec.adl_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, GlobalTheory.CellDec.adl_add]

theorem det_finGL' {E : Type} [Field E] [NumberField E] {a : ℕ} (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  let p : Ad E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (Af E)
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map p (finGL E a k)
    have h0 : GeneralLinearGroup.map p (finGL E a k) = 1 :=
      map_cornerGL_of_zero (sFin E) p (fun x => rfl) k
    rw [h0, map_one, Units.val_one] at h
    change p _ = _
    rw [← h]
    change (1 : InfiniteAdeleRing E) = (1 : InfiniteAdeleRing E) - 0 + 0
    simp
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    have h0 : GeneralLinearGroup.map (pFin E) (finGL E a k) = GeneralLinearGroup.map (RingHom.id _) k :=
      map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun x => rfl) k
    rw [h0] at h
    change pFin E _ = _
    rw [← h]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    rw [sub_self, zero_add]
    rfl

end GlobalTheory.CellDec.DetMod

theorem GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  intro E _ _ n ϖ hϖ l g
  rw [map_mul, map_mul, Positive.val_mul]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.SmGL.diagT (Af E) (Fin n)
      fun i => GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) =
      ∏ i, GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal, Units.coe_prod]
  unfold GlobalTheory.CellDec.tl
  rw [GlobalTheory.CellDec.DetMod.det_finGL', hdet, GlobalTheory.CellDec.DetMod.prod_adl]
  rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support]
  · refine Finset.prod_congr rfl fun v _ => ?_
    congr 2
    rw [Finsupp.finsetSum_apply]
    rfl
  · intro v hv
    rw [Finsupp.notMem_support_iff] at hv
    rw [Finsupp.finsetSum_apply]
    simp [hv]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_doubledLagrangian_of_rational_unitary_frame : ∀ (D : D7) (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∃ Y : Lag W, IsLagFrame W Y (frameOf W g₀) := by
  first | exact @GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf | exact GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf | (intros; apply GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubledLagrangian_eq_iff_siegelParabolic_coset : ∀ (D : D7) (W : HSp D) (γ γ' : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) (g₀' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ' = g₀'.map (incA D) → ∀ (Y Y' : Lag W), IsLagFrame W Y (frameOf W g₀) → IsLagFrame W Y' (frameOf W g₀') → (Y = Y' ↔ γ' * γ⁻¹ ∈ GlobalTheory.Doubling.siegel W) := by
  first | exact @GlobalTheory.SWLagSame.sameClass | exact GlobalTheory.SWLagSame.sameClass | (intros; apply GlobalTheory.SWLagSame.sameClass <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam := by
  first | exact @GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU | exact GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU | (intros; apply GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU <;> assumption)
end
