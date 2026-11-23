module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.EpsRedFr

theorem epsRed_tangent_frX : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D r))) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P := by
  intro E _ _ _ H Dw l Xo c TF U D K _ _ P hU y' hU' hy hev
  have h1 : ⊤ ≤ ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) ⁻¹ᵁ U.1 := by
    rw [Category.assoc]; exact GlobalTheory.FlagMod.le_preimage_comp _ hU'
  have hfst : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap c.F (DualNumber K)) = algebraMap c.F K :=
    RingHom.ext fun r => by simp
  refine GlobalTheory.FlagMod.xF_ext (Y := TF.Y) ?_ (GlobalTheory.FlagMod.frX_snd P) ?_
  · rw [Category.assoc, hy, GlobalTheory.DeRham.epsRed, spMap_comp', hfst]
  · have e : ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.1 h1 = ev (frX P ≫ TF.Y.j) U.1 hU := by
      have e0 : ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.1 h1 =
          (TrivSqZeroExt.fstHom K K K).toRingHom.comp (ev (y' ≫ TF.Y.j) U.1 hU') := by
        rw [← GlobalTheory.FlagMod.ev_spMap _ (y' ≫ TF.Y.j) U.1 hU' (by rw [← Category.assoc]; exact h1)]
        exact GlobalTheory.FlagMod.ev_congr (Category.assoc _ _ _) _ _ _
      rw [e0]
      refine RingHom.ext fun r => ?_
      rw [RingHom.comp_apply, hev r]
      simp
    rw [← GlobalTheory.FlagMod.spMap_ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.2 h1,
      ← GlobalTheory.FlagMod.spMap_ev (frX P ≫ TF.Y.j) U.2 hU, e]

end GlobalTheory.EpsRedFr
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer.LogDer

open Filter Topology

theorem logDer_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f c d : E → ℂ} {z : E}
    (h : f =ᶠ[𝓝 z] fun w => c w * d w) (hc : DifferentiableAt ℂ c z) (hd : DifferentiableAt ℂ d z)
    (hc0 : c z ≠ 0) (hd0 : d z ≠ 0) (v : E) :
    fderiv ℂ f z v / f z = fderiv ℂ c z v / c z + fderiv ℂ d z v / d z := by
  have hm : HasFDerivAt (fun w => c w * d w) (c z • fderiv ℂ d z + d z • fderiv ℂ c z) z :=
    hc.hasFDerivAt.mul hd.hasFDerivAt
  rw [h.fderiv_eq, hm.fderiv, h.eq_of_nhds]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem hasFDerivAt_factor {g : ℕ} (a b c : ℂ) (m z : Fin g → ℂ) :
    ∃ D : (Fin g → ℂ) →L[ℂ] ℂ, HasFDerivAt (fun w : Fin g → ℂ => a * Complex.exp (b * (w ⬝ᵥ m) + c)) D z ∧
      ∀ v, D v = a * Complex.exp (b * (z ⬝ᵥ m) + c) * (b * (v ⬝ᵥ m)) := by

  let ℓ : (Fin g → ℂ) →L[ℂ] ℂ := ∑ i, m i • ContinuousLinearMap.proj i
  have hℓ : ∀ w, ℓ w = w ⬝ᵥ m := by
    intro w
    simp [ℓ, dotProduct, mul_comm]
  have H := (((ℓ.hasFDerivAt (x := z)).const_mul b).add_const c).cexp.const_mul a
  have hfun : (fun w : Fin g → ℂ => a * Complex.exp (b * (w ⬝ᵥ m) + c)) = fun w => a * Complex.exp (b * ℓ w + c) := by
    funext w
    rw [hℓ]
  refine ⟨a • (Complex.exp (b * ℓ z + c) • (b • ℓ)), ?_, ?_⟩
  · rw [hfun]
    exact H
  · intro v
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hℓ]
    ring

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → L.IsLB → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH H χ → ∀ v : Fin g → ℂ, (∀ i, DifferentiableOn ℂ (fun z => fderiv ℂ (u.fr i) z v / u.fr i z) (pre u.ex (L.U i))) ∧ (∀ i j, IsReg u.ex (L.U i ⊓ L.U j) ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z)) ∧ ∀ i (l : u.Λ), ∀ z ∈ pre u.ex (L.U i), fderiv ℂ (u.fr i) (z + l) v / u.fr i (z + l) = fderiv ℂ (u.fr i) z v / u.fr i z - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  intro A _ g L u hA _ H χ hAH v
  obtain ⟨hopen, hdval, hshift, -, hinf, -, -, -, -, hev, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u

  have hfrd : ∀ i, DifferentiableOn ℂ (u.fr i) (pre u.ex (L.U i)) := u.10
  have hfr0 : ∀ i, ∀ z ∈ pre u.ex (L.U i), u.fr i z ≠ 0 := fun i z hz => u.11 i z hz
  have hfrg : ∀ i j, ∀ z ∈ pre u.ex (L.U i ⊓ L.U j),
      u.fr i z = val u.ex (L.U i ⊓ L.U j) (L.g i j : Γ(A.left, L.U i ⊓ L.U j)) z * u.fr j z :=
    fun i j z hz => u.12 i j z hz
  have hfra : ∀ i, ∀ z ∈ pre u.ex (L.U i), DifferentiableAt ℂ (u.fr i) z :=
    fun i z hz => (hfrd i).differentiableAt ((hopen _).mem_nhds hz)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i z hz

    let e : ReciprocityTheory.L2DbarEstimates.V g ≃L[ℂ] (Fin g → ℂ) := EuclideanSpace.equiv (Fin g) ℂ
    have hpre : IsOpen (e ⁻¹' pre u.ex (L.U i)) := (hopen _).preimage e.continuous
    have hsm := ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn g (u.fr i ∘ e) _ hpre
      ((hfrd i).comp e.differentiableOn (fun y hy => hy))
    have hsm' : ContDiffOn ℂ (↑(⊤ : ℕ∞)) (u.fr i) (pre u.ex (L.U i)) := by
      have h2 := hsm.comp e.symm.contDiff.contDiffOn (fun y hy => by simpa using hy)
      have h3 : (u.fr i ∘ e) ∘ e.symm = u.fr i := by
        funext y
        simp
      rwa [h3] at h2
    have hca := (hsm'.contDiffAt ((hopen _).mem_nhds hz)).fderiv_right (m := 1)
      (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
    have h1 : DifferentiableAt ℂ (fun w => fderiv ℂ (u.fr i) w v) z :=
      (hca.differentiableAt one_ne_zero).clm_apply (differentiableAt_const v)
    have h4 := h1.mul ((hfra i z hz).inv (hfr0 i z hz))
    simp only [div_eq_mul_inv]
    exact h4.differentiableWithinAt
  ·
    intro i j
    set U := L.U i ⊓ L.U j with hU
    set G : Γ(A.left, U) := (L.g i j).val with hG
    set G' : Γ(A.left, U) := ((L.g i j)⁻¹ : (Γ(A.left, U))ˣ).val with hG'
    obtain ⟨-, hring, hcongr, -, -, -⟩ := GlobalTheory.T.isRegularOnOpenUniformised_subalgebra_restrict A g L u U
    have hder : IsReg u.ex U fun z => fderiv ℂ (val u.ex U G) z v := GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised A g L u hA U G v
    have hinv : IsReg u.ex U (val u.ex U G') := ⟨G', fun z _ => rfl⟩
    have hprod := (hring _ _ hder hinv).2.2
    refine hcongr _ _ hprod ?_
    intro z hz
    have hzij : z ∈ pre u.ex (L.U i) ∩ pre u.ex (L.U j) := by rw [← hinf]; exact hz
    have hGG : val u.ex U G z * val u.ex U G' z = 1 := by
      obtain ⟨e, he⟩ := hev U z hz
      have h1 : G * G' = 1 := Units.mul_inv _
      rw [he, he]
      exact (map_mul e G G').symm.trans ((congrArg e h1).trans (map_one e))
    have hG0 : val u.ex U G z ≠ 0 := left_ne_zero_of_mul_eq_one hGG
    have hev' : ∀ᶠ w in 𝓝 z, u.fr i w = val u.ex U G w * u.fr j w :=
      Filter.eventually_of_mem ((hopen U).mem_nhds hz) (fun w hw => hfrg i j w hw)
    have key := logDer_mul hev' ((hdval U G).differentiableAt ((hopen U).mem_nhds hz))
      (hfra j z hzij.2) hG0 (hfr0 j z hzij.2) v
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [key, eq_inv_of_mul_eq_one_right hGG]
    ring
  ·
    intro i l z hz
    set m := H.mulVec (star (l : Fin g → ℂ)) with hm
    have hzl : z + (l : Fin g → ℂ) ∈ pre u.ex (L.U i) := (hshift (L.U i) l z).2 hz
    have hχ : χ l ≠ 0 := by
      intro h0
      have := hAH.2.2.1 l
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    obtain ⟨D, hD, hDv⟩ := hasFDerivAt_factor (χ l) (Real.pi : ℂ) ((Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m)) m z
    have hev' : ∀ᶠ w in 𝓝 z, u.fr i w = (χ l * Complex.exp ((Real.pi : ℂ) * (w ⬝ᵥ m) + (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m))) * u.fr i (w + l) :=
      Filter.eventually_of_mem ((hopen _).mem_nhds hz) (fun w hw => hAH.2.2.2 l i w hw)
    have hdl : DifferentiableAt ℂ (fun w => u.fr i (w + l)) z :=
      (hfra i _ hzl).comp z (differentiableAt_id.add_const _)
    have key := logDer_mul hev' hD.differentiableAt hdl
      (mul_ne_zero hχ (Complex.exp_ne_zero _)) (hfr0 i _ hzl) v
    rw [hD.fderiv, hDv, fderiv_comp_add_right] at key
    have hE : χ l * Complex.exp ((Real.pi : ℂ) * (z ⬝ᵥ m) + (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m)) ≠ 0 :=
      mul_ne_zero hχ (Complex.exp_ne_zero _)
    rw [key, mul_div_cancel_left₀ _ hE]
    ring

end GlobalTheory.CechPer.LogDer
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

namespace GlobalTheory.InvSys

theorem exists_nsmul_of_basis {M κ : Type} [AddCommGroup M] (b : Module.Basis κ ℤ M) (f : M →ₗ[ℤ] M) (n : ℕ)
    (hb : ∀ i, ∃ z, f (b i) = n • z) (x : M) : ∃ z, f x = n • z := by
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hb i
  | zero => exact ⟨0, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨z1, h1⟩ := hy; obtain ⟨z2, h2⟩ := hw
    exact ⟨z1 + z2, by rw [map_add (f := _), h1, h2, smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨z, h⟩ := hy
    exact ⟨a • z, by rw [map_smul, h, smul_comm]⟩

theorem invSys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w) → ∃ g' : ℕ → D.La →+ D.La, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g' (n * m) x = g' n x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g' n (g n x) = x + n • z) := by
  intro p _ D g htow hsurj hinj
  haveI := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  choose y z hyz using hsurj
  let g' : ℕ → D.La →+ D.La := fun n =>
    if h : 0 < n ∧ n.Coprime p then (b.constr ℤ (fun i => y n h.1 h.2 (b i))).toAddMonoidHom else 0
  have sec : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z := by
    intro n hn hc x
    have hg' : g' n = (b.constr ℤ (fun i => y n hn hc (b i))).toAddMonoidHom := by
      simp only [g', dif_pos (And.intro hn hc)]
    obtain ⟨w, hw⟩ := exists_nsmul_of_basis b
      ((g n).toIntLinearMap ∘ₗ b.constr ℤ (fun i => y n hn hc (b i)) - LinearMap.id) n
      (fun i => ⟨z n hn hc (b i), by simp [Module.Basis.constr_basis, hyz]⟩) x
    refine ⟨w, ?_⟩
    rw [hg']
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply] at hw
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [← hw]; abel
  refine ⟨g', ?_, sec, ?_⟩
  · intro n m hn hm hc x
    have hcn : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hc
    obtain ⟨z1, h1⟩ := htow n m hn hm hc (g' (n * m) x)
    obtain ⟨z2, h2⟩ := sec (n * m) (Nat.mul_pos hn hm) hc x
    obtain ⟨z3, h3⟩ := sec n hn hcn x
    obtain ⟨w, hw⟩ := hinj n hn hcn (g' (n * m) x - g' n x) (m • z2 - z1 - z3) (by
      rw [map_sub, smul_sub, smul_sub]
      rw [h2] at h1
      have : g n (g' (n * m) x) = x + (n * m) • z2 - n • z1 := by rw [h1]; abel
      rw [this, h3]
      rw [mul_smul]; abel)
    exact ⟨w, by rw [← hw]; abel⟩
  · intro n hn hc x
    obtain ⟨z1, h1⟩ := sec n hn hc (g n x)
    obtain ⟨w, hw⟩ := hinj n hn hc (g' n (g n x) - x) z1 (by rw [map_sub, h1]; abel)
    exact ⟨w, by rw [← hw]; abel⟩

end GlobalTheory.InvSys
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_variety_wedge_no_primitive_h2 : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A := by
  first | exact @GlobalTheory.AbCoh.wedgeO_noPrimO2 | exact GlobalTheory.AbCoh.wedgeO_noPrimO2 | (intros; apply GlobalTheory.AbCoh.wedgeO_noPrimO2 <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevOrbit

def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Submodule R M) (f g : M →ₗ[R] M)
    (hK : ∀ a ∈ K, f a ∈ K) (hK' : ∀ a ∈ K, g a ∈ K) (hfg : ∀ a, f (g a) - a ∈ K) (hgf : ∀ a, g (f a) - a ∈ K) :
    (M ⧸ K) ≃ₗ[R] (M ⧸ K) :=
  LinearEquiv.ofLinear (K.mapQ K f (fun a ha => hK a ha)) (K.mapQ K g (fun a ha => hK' a ha))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hfg a))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hgf a))

theorem smul_top_comap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    ∀ a ∈ (I • ⊤ : Submodule R M), f a ∈ (I • ⊤ : Submodule R M) := by
  have h : (I • ⊤ : Submodule R M) ≤ (I • ⊤ : Submodule R M).comap f := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact fun a ha => h ha

theorem exists_gam_of_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (g : Sim Dw) :
    ∃ γ : Gam Dw l₂, ∀ a, γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f l₂.M a) := by
  obtain ⟨h, hh⟩ := g.inv l₂.M (GlobalTheory.LevelFibre.level_pos l₂)
  exact ⟨quotEquiv _ (g.f l₂.M) h (smul_top_comap _ _) (smul_top_comap _ _)
    (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).2) (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).1),
    fun a => rfl⟩

theorem fibre_torsor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → (FrOver d y₂' y ↔ ∃ γ, CongMod l.Mb (lift γ) LinearMap.id ∧ levR (lift γ, LinearMap.id) y₂ y₂') ∧ ∀ γ γ', levR (lift γ, LinearMap.id) y₂ y₂' → levR (lift γ', LinearMap.id) y₂ y₂' → γ = γ' := by
  intro E _ _ _ H Dw l Xo c d hpq hlev hA hbase lift hlift k _ _ _ _ hk y₂ y₂' y hy
  obtain ⟨hd, hM, -, -, -, hE, -, -, -⟩ := id hlev
  have hLaws : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hN := GlobalTheory.levelMaps_closed hLaws E H Dw hpq
  refine ⟨⟨fun h' => ?_, fun ⟨γ, hγ, hr⟩ => ?_⟩, fun γ γ' h₁ h₂ => GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique E H Dw d.l₂ d.Xo₂ d.c₂ hpq hA lift hlift k y₂ y₂' γ γ' h₁ h₂⟩
  · obtain ⟨g, ρ, ν, hg, -, hmv, hfr⟩ :=
      GlobalTheory.exists_levMove_of_frOver hLaws E H Dw l Xo c 0 d hN hd hM hE d.r d.m hE k hk y y₂ y₂' hy h'
    obtain ⟨γ, hγ⟩ := exists_gam_of_sim d.l₂ g
    have hl : ∀ a, lift γ a - g.f d.l₂.M a ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
      have e := congrArg (fun f => f a) (hlift γ)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, hγ] at e
      exact (Submodule.Quotient.eq _).1 e
    refine ⟨γ, fun a => ?_, (GlobalTheory.LevelActionOfLifts.levR_congr hl y₂ y₂').2 ⟨ρ.hom, ν, inferInstance,
      ⟨hmv.1, hmv.2.1, fun a => ?_⟩, hfr⟩⟩
    · have h1 : lift γ a - g.f d.l₂.M a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
        Submodule.smul_mono_left hd.2.1 (hl a)
      have h2 := GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg a
      have := Submodule.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at this
    · have e : ∀ x x', d.Xo₂.univ.etaA x = d.Xo₂.univ.etaA x' := fun x x' => by
        have h1 := d.Xo₂.univ.etaA_ker x
        have h2 := d.Xo₂.univ.etaA_ker x'
        rw [hA, one_smul] at h1 h2
        rw [h1, h2]
      rw [e (LinearMap.id a) (g.f d.l₂.A a)]
      exact hmv.2.2 a
  · obtain ⟨ρ₂, ν₂, hi, hmv, hfr⟩ := hr
    obtain ⟨e₁, e₂⟩ := GlobalTheory.T.levMove_comp_r_eq_of_trivial_mod E H Dw l Xo c 0 d hpq hlev hA hbase ρ₂ ν₂ (lift γ) LinearMap.id hi hmv hγ
    obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
    exact GlobalTheory.frOver_of_square_of_frMove E H Dw l Xo c 0 d (𝟙 _) ι ρ₂ ν₂ d.r d.m (by rw [e₁, Category.comp_id])
      (by rw [e₂, hι, Category.comp_id]) k y y y₂ y₂' hy (hone k y) hfr

end GlobalTheory.LevOrbit
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.surjective_twistedKernel_additiveLineBundleFamily : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → Surjective (h ≫ snd A T).left := by
  first | exact @GlobalTheory.TwistKerSurj.surjective_twist_kernel | exact GlobalTheory.TwistKerSurj.surjective_twist_kernel | (intros; apply GlobalTheory.TwistKerSurj.surjective_twist_kernel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_weilDatum_of_splittingCharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), (∃ η, IsEtaTilde D η) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, IsWeilDatumO ψ S T χS χT om := by
  first | exact @GlobalTheory.WeilExist.exists_isWeilDatumO | exact GlobalTheory.WeilExist.exists_isWeilDatumO | (intros; apply GlobalTheory.WeilExist.exists_isWeilDatumO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → IsWeilDatumO ψ S T χS χT om → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → ∀ x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → om (g, h) f = (((((χT * (η ^ T.rank)⁻¹) x)⁻¹ * (χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) * ∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f := by
  first | exact @GlobalTheory.WeilVacChar.vacuum_character | exact GlobalTheory.WeilVacChar.vacuum_character | (intros; apply GlobalTheory.WeilVacChar.vacuum_character <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), (∃ η, IsEtaTilde D η) → IsWeilDatumO ψ S T χS χT om → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε := by
  first | exact @GlobalTheory.VacInert.fixesVacAt_of_unram | exact GlobalTheory.VacInert.fixesVacAt_of_unram | (intros; apply GlobalTheory.VacInert.fixesVacAt_of_unram <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_fockMap_signatures_depend_on_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  exact GlobalTheory.HoweD.exists_isFockMapD F E σ α β κ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isCompact_definiteUnitary_restricted_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) → IsCompact {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  first | exact @GlobalTheory.BCT.LocCpt.loc_cpt | exact GlobalTheory.BCT.LocCpt.loc_cpt | (intros; apply GlobalTheory.BCT.LocCpt.loc_cpt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.flagCell_coords_bijective_onto_chart_prod : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  first | exact @GlobalTheory.FlagCell2.cellMap_image_eq | exact GlobalTheory.FlagCell2.cellMap_image_eq | (intros; apply GlobalTheory.FlagCell2.cellMap_image_eq <;> assumption)
end
