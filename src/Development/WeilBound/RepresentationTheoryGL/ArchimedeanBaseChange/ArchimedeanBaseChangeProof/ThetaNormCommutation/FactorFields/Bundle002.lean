module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.TensorComplP

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F))

theorem finite_over : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 F) = v}.Finite := by
  have := v.isMaximal
  have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine (h.preimage (f := HeightOneSpectrum.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

def phi : v.adicCompletion F ⊗[F] K →+*
    (∀ u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}, u.1.adicCompletion K) :=
  RingHom.pi fun u => GlobalTheory.LFun.toCompl u.2

theorem phi_apply (y : v.adicCompletion F ⊗[F] K) (u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}) :
    phi v y u = GlobalTheory.LFun.toCompl u.2 y := rfl

def extZ : v.adicCompletion F ⊗[F] K →ₗ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] K :=
  LinearMap.rTensor K (GlobalTheory.AdelicU.singleFin v)

theorem map_extZ_self (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) (extZ v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem map_extZ_ne {v' : HeightOneSpectrum (𝓞 F)} (h : v' ≠ v) (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F K) (extZ v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, TensorProduct.zero_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]

theorem phi_injective : Function.Injective (phi (K := K) v) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have h0 : GlobalTheory.LFun.finAdEquiv F K (extZ v y) = 0 := by
    have hc : ∀ w : HeightOneSpectrum (𝓞 K), GlobalTheory.LFun.finAdEquiv F K (extZ v y) w = 0 := by
      intro w
      by_cases hw : w.under (𝓞 F) = v
      · rw [GlobalTheory.LFun.finAdEquiv_apply hw, map_extZ_self]
        exact (phi_apply v y ⟨w, hw⟩).symm.trans (congrFun hy ⟨w, hw⟩)
      · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, map_extZ_ne v hw, map_zero]
    exact Subtype.ext (funext hc)
  have h1 : extZ v y = 0 := (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv F K).injective).1 h0
  rw [← map_extZ_self v y, h1, map_zero]

theorem phi_surjective : Function.Surjective (phi (K := K) v) := by
  intro z
  obtain ⟨y, hy⟩ := (GlobalTheory.LFun.finAdEquiv F K).surjective
    ⟨fun w => if h : w.under (𝓞 F) = v then z ⟨w, h⟩ else 0, by
      filter_upwards [(finite_over (K := K) v).compl_mem_cofinite] with u hu
      rw [dite_eq_right (by simpa using hu)]
      exact zero_mem _⟩
  refine ⟨Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) y, funext fun u => ?_⟩
  rw [phi_apply, ← GlobalTheory.LFun.finAdEquiv_apply u.2, hy]
  show (if h : u.1.under (𝓞 F) = v then z ⟨u.1, h⟩ else 0) = z u
  rw [dite_eq_left u.2]

end PositivityTheory.Rg.BcB.G3.TensorComplP

open PositivityTheory.Rg.BcB.G3.TensorComplP in
theorem PositivityTheory.Rg.BcB.G3.tensorCompl_pf : TensorCompl := by
  intro F K _ _ _ _ _ v
  refine ⟨RingEquiv.ofBijective (phi v) ⟨phi_injective v, phi_surjective v⟩, fun a u => ?_⟩
  show GlobalTheory.LFun.toCompl u.2 (1 ⊗ₜ[F] a) = _
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.GenUnitP

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  rw [hR, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun q hq => absurd (Subsingleton.elim q 1) hq)]
  simp

theorem ind_const {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * y * θ (x * k))) =
      fun _ => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * y * θ x) := by
  funext k
  have e : (x * (k : G))⁻¹ * y * θ (x * k) = (k : G)⁻¹ * (x⁻¹ * y * θ x) * θ k := by
    simp only [map_mul, _root_.mul_inv_rev]; group
  rw [e]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from
      K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) (hKθ _ k.2)), Set.indicator_of_mem (show _ ∈ (K : Set G) from hm)]
    rfl
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), Set.indicator_of_notMem]
    intro h
    apply hm
    have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem (hKθ _ k.2))
    simpa [mul_assoc] using this

theorem summand_eq {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    GlobalTheory.TwOrbConj.summand θ K y ((K : Set G).indicator 1) x =
      if x⁻¹ * y * θ x ∈ K then
        (((twCent θ y ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) else 0 := by
  unfold GlobalTheory.TwOrbConj.summand
  rw [ind_const θ K hKθ y x, avg_const]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from hm), if_pos hm]; simp
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), if_neg hm]; simp

end PositivityTheory.Rg.BcB.G3.GenUnitP

theorem PositivityTheory.Rg.BcB.G3.genUnit_pf : PositivityTheory.Rg.BcB.G3.GenUnit := by
  intro G _ _ _ θ K z hKθ hzK huniq hcptK g
  have hidx : ∀ x : G, (rStab fun k : K =>
      (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * z * θ (x * k))).index ≠ 0 := by
    intro x
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.ind_const θ K hKθ z x]
    have : rStab (fun _ : K => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * z * θ x)) = ⊤ := by
      ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
    rw [this, Subgroup.index_top]
    exact one_ne_zero
  rw [GlobalTheory.TwOrbConj.twOrb_twConj G θ K z g ((K : Set G).indicator 1) hidx]
  have hcpt : cptPart (twCent θ z) ≤ twCent θ z ⊓ K :=
    le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1)
      ((Subgroup.closure_le _).2 fun t ht => hcptK t ht.1 ht.2)
  have hval : GlobalTheory.TwOrbConj.summand θ K z ((K : Set G).indicator 1) 1 = 1 := by
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z 1, if_pos (by simpa using hzK),
      GlobalTheory.TwOrbConj.map_conj_self K (K.one_mem), (Subgroup.relIndex_eq_one).2 hcpt]
    simp
  rw [GlobalTheory.TwOrbConj.twOrb_eq, finsum_eq_single _ (DoubleCoset.mk (twCent θ z) K 1)]
  · obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk (twCent θ z) K 1)).symm
    rw [he, GlobalTheory.TwOrbConj.summand_rep θ K z _ 1 ht hk, hval]
  · intro q hq
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z]
    split_ifs with hm
    · exfalso
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := huniq _ hm
      symm
      conv_rhs => rw [← DoubleCoset.out_eq' q]
      rw [DoubleCoset.eq]
      exact ⟨t, ht, k, hk, by rw [he]; group⟩
    · rfl
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.BaseFrameP

theorem phi_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map p = GlobalTheory.Tw.Phi n S := by
  ext i k
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

end PositivityTheory.Rg.BcB.G3.BaseFrameP

open PositivityTheory.Rg.BcB.G3.BaseFrameP in
theorem PositivityTheory.Rg.BcB.G3.baseFrame_pf : BaseFrame := by
  intro F E F' E' _ _ _ _ _ _ _ p j c c' s d hj hc hcj hs0 hcs hspE hspE' n δ hsep B _ _ ρ hfr
  have hps0 : p s ≠ 0 := (map_ne_zero p).2 hs0
  have hcps : c' (p s) = - p s := by rw [hc, hcs, map_neg]
  have indep' : ∀ u v : F', j u + p s * j v = 0 → u = 0 ∧ v = 0 := by
    intro u v h
    have h2 := congrArg c' h
    simp only [map_add (f := _), map_mul, hcj, hcps, map_zero] at h2
    have hu : j u = 0 := by
      have h3 : (2 : E') * j u = 0 := by linear_combination h + h2
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
    have hv : j v = 0 := by
      rw [hu, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left hps0
    exact ⟨(map_eq_zero j).1 hu, (map_eq_zero j).1 hv⟩
  have indepE : ∀ a b : F, algebraMap F E a + s * algebraMap F E b = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h1 := congrArg p h
    simp only [map_add (f := _), map_mul, ← hj, map_zero] at h1
    obtain ⟨h2, h3⟩ := indep' _ _ h1
    exact ⟨(map_eq_zero (algebraMap F F')).1 h2, (map_eq_zero (algebraMap F F')).1 h3⟩
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    apply indepE a b
    simp only [Algebra.smul_def] at h
    linear_combination h
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), s]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspE z
    have h1 : (1 : E) ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨0, rfl⟩
    have h2 : s ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨1, rfl⟩
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ a h1) (Submodule.smul_mem _ b h2)
    convert h3 using 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  obtain ⟨bE, hb0, hb1⟩ : ∃ bE : Module.Basis (Fin 2) F E, bE 0 = 1 ∧ bE 1 = s :=
    ⟨Module.Basis.mk hli hsp, by simp, by simp⟩
  have hdec : ∀ e : E, e = algebraMap F E (bE.repr e 0) + s * algebraMap F E (bE.repr e 1) := by
    intro e
    conv_lhs => rw [← bE.sum_repr e]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def]
    ring
  have hsq : ρ (algebraMap F B d) = s ^ 2 • (1 : Matrix (Fin n) (Fin n) E) := hfr.sq
  have hadj : ∀ a, ρ a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((ρ a).map c)ᵀ := hfr.adj
  have hcm : ∀ a, ρ a * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * ρ a := hfr.comm

  obtain ⟨ρ', hρt⟩ : ∃ ρ' : F' ⊗[F] B →+* Matrix (Fin n) (Fin n) E',
      ∀ x b, ρ' (x ⊗ₜ b) = j x • (ρ b).map p := by
    let _ : Algebra F E' := (p.comp (algebraMap F E)).toAlgebra
    let pA : E →ₐ[F] E' := { p with commutes' := fun _ => rfl }
    let fA : F' →ₐ[F] Matrix (Fin n) (Fin n) E' :=
      { (Matrix.scalar (Fin n) : E' →+* Matrix (Fin n) (Fin n) E').comp j with
        commutes' := fun x => by
          show Matrix.scalar (Fin n) (j (algebraMap F F' x)) = _
          rw [hj, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
          rfl }
    let gA : B →ₐ[F] Matrix (Fin n) (Fin n) E' := pA.mapMatrix.comp ρ
    have hcomm : ∀ x y, Commute (fA x) (gA y) := fun x y => by
      show Commute (Matrix.scalar (Fin n) (j x)) _
      exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    refine ⟨(Algebra.TensorProduct.lift fA gA hcomm).toRingHom, fun x b => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
    show Matrix.scalar (Fin n) (j x) * (ρ b).map p = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hρ1 : ∀ a, ρ' (1 ⊗ₜ a) = (ρ a).map p := by
    intro a; rw [hρt, map_one, one_smul]
  have hρu : ∀ u : F', ρ' (u ⊗ₜ (1 : B)) = j u • (1 : Matrix (Fin n) (Fin n) E') := by
    intro u; rw [hρt, map_one ρ, Matrix.map_one _ (map_zero p) (map_one p)]
  have hD : ρ' ((1 : F') ⊗ₜ algebraMap F B d) = (p s) ^ 2 • (1 : Matrix (Fin n) (Fin n) E') := by
    rw [hρ1, hsq]
    ext i k
    by_cases h : i = k <;> simp [h, Matrix.one_apply]
  have hN' : (GeneralLinearGroup.map p δ * thetaGL n c' (GeneralLinearGroup.map p δ)).val =
      (δ * thetaGL n c δ).val.map p := by
    rw [← GlobalTheory.ThetaPull.map_thetaGL p c c' (fun x => (hc x).symm) δ, ← map_mul]
    rfl
  refine ⟨ρ', hρ1, ⟨?_, hD, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨φ, hφdef⟩ : ∃ φ : B →ₗ[F] (Fin n × Fin n × Fin 2 → F),
        ∀ b i, φ b i = bE.repr (ρ b i.1 i.2.1) i.2.2 :=
      ⟨{ toFun := fun b i => bE.repr (ρ b i.1 i.2.1) i.2.2
         map_add' := fun a b => by funext i; simp [map_add (f := _)]
         map_smul' := fun r b => by funext i; simp [map_smul] }, fun _ _ => rfl⟩
    have hφ : Function.Injective φ := by
      refine (injective_iff_map_eq_zero φ).2 fun b hb => ?_
      have h1 : ρ b = 0 := by
        ext i k
        have h2 : bE.repr (ρ b i k) = 0 := by
          ext t
          have := congrFun hb (i, k, t)
          rw [hφdef] at this
          simpa using this
        simpa using h2
      exact (injective_iff_map_eq_zero ρ.toRingHom).1 hfr.inj b h1
    have hL : Function.Injective (φ.lTensor F') := Module.Flat.lTensor_preserves_injective_linearMap φ hφ
    have hkey : ∀ X : F' ⊗[F] B, ∀ i k, ρ' X i k =
        j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 0)) +
        p s * j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 1)) := by
      intro X i k
      induction X using TensorProduct.induction_on with
      | zero => simp
      | tmul x b =>
        rw [hρt]
        simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
          TensorProduct.piScalarRightHom_tmul, hφdef, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        conv_lhs => rw [hdec (ρ b i k)]
        simp only [map_add (f := _), map_mul, ← hj]
        ring
      | add X Y hX hY =>
        simp only [map_add (f := _), Matrix.add_apply, hX, hY, Pi.add_apply]
        ring
    refine (injective_iff_map_eq_zero ρ').2 fun X hX => ?_
    have hW : TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) = 0 := by
      funext ⟨i, k, t⟩
      have h := hkey X i k
      rw [hX, Matrix.zero_apply] at h
      obtain ⟨h0, h1⟩ := indep' _ _ h.symm
      have ht : t = 0 ∨ t = 1 := by fin_cases t <;> simp
      rcases ht with rfl | rfl
      · exact h0
      · exact h1
    have h0 : φ.lTensor F' X = 0 :=
      (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2)).injective (hW.trans (map_zero _).symm)
    exact hL (by rw [h0, map_zero])
  ·
    intro X
    rw [show (GeneralLinearGroup.map p δ).val = δ.val.map p from rfl, ← phi_map p n, ← Matrix.map_mul]
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt]
      have e1 : ((j x • (ρ b).map p).map c') = j x • (((ρ b).map c).map p) := by
        ext i k; simp [hcj, hc]
      rw [e1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [← Matrix.map_mul, hadj, ← Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
    | add X Y hX hY =>
      rw [map_add (f := _), add_mul, hX, hY, Matrix.map_add _ (map_add c'), Matrix.transpose_add, mul_add]
  ·
    intro X
    rw [hN']
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, hcm]
    | add X Y hX hY =>
      rw [map_add (f := _), add_mul, mul_add, hX, hY]
  ·
    intro x hx
    rw [hN'] at hx
    have hsepN' : ((δ * thetaGL n c δ).val.map p).charpoly.Separable := by
      rw [Matrix.charpoly_map]; exact hsep.map
    obtain ⟨q, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm _ x hsepN' hx.symm
    have hTadd : ∀ y z : Matrix (Fin n) (Fin n) E', (∃ a b, y = ρ' a + p s • ρ' b) →
        (∃ a b, z = ρ' a + p s • ρ' b) → ∃ a b, y + z = ρ' a + p s • ρ' b := by
      rintro y z ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
      exact ⟨a + a', b + b', by rw [map_add (f := _), map_add (f := _), smul_add]; abel⟩
    have hT0 : ∃ a b, (0 : Matrix (Fin n) (Fin n) E') = ρ' a + p s • ρ' b := ⟨0, 0, by simp⟩
    have hTsmul : ∀ (e : E') (y : Matrix (Fin n) (Fin n) E'), (∃ a b, y = ρ' a + p s • ρ' b) →
        ∃ a b, e • y = ρ' a + p s • ρ' b := by
      rintro e y ⟨a, b, rfl⟩
      obtain ⟨u, v, rfl⟩ := hspE' e
      refine ⟨(u ⊗ₜ (1 : B)) * a + ((1 : F') ⊗ₜ algebraMap F B d) * ((v ⊗ₜ (1 : B)) * b),
        (u ⊗ₜ (1 : B)) * b + (v ⊗ₜ (1 : B)) * a, ?_⟩
      simp only [map_add (f := _), map_mul, hρu, hD, Matrix.smul_mul, one_mul]
      module
    have hTpow : ∀ k : ℕ, ∃ a b, ((δ * thetaGL n c δ).val.map p) ^ k = ρ' a + p s • ρ' b := by
      intro k
      obtain ⟨a, b, hab⟩ := hfr.span ((δ * thetaGL n c δ).val ^ k)
        (Commute.self_pow (δ * thetaGL n c δ).val k).eq.symm
      refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_⟩
      have hpw : ((δ * thetaGL n c δ).val.map p) ^ k = ((δ * thetaGL n c δ).val ^ k).map p :=
        (map_pow p.mapMatrix _ k).symm
      rw [hpw, hρ1, hρ1, hab]
      ext i k
      simp
    rw [aeval_eq_sum_range]
    exact Finset.sum_induction _ (fun y => ∃ a b, y = ρ' a + p s • ρ' b) hTadd hT0
      (fun i _ => hTsmul _ _ (hTpow i))
end
end
