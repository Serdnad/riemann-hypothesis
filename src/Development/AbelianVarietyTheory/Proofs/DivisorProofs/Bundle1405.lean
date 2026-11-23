module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilled
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle324
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem finiteType_int_of_isAffineOpen {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  obtain ⟨N, i, hi, e⟩ := hX.isProjOver
  have : LocallyOfFiniteType p := by subst e; infer_instance
  have : Module.Finite ℤ k := hX.finite
  have h1 := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp k)) hU (by simp)
  have h2 : (algebraMap ℤ k).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  have h3 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).FiniteType :=
    RingHom.FiniteType.of_surjective _ fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x, by simp⟩
  have h4 := h1.comp (h3.comp h2)
  rw [← RingHom.finiteType_algebraMap]
  convert h4 using 1
  exact RingHom.ext_int _ _

theorem Pair.max_principle_near : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∀ (σ : k →+* ℂ) (y₀ : CxPts p σ), ∃ (W : Set (CxPts p σ)) (ρ : ℝ), W ∈ 𝓝 y₀ ∧ 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ' : k →+* ℂ) (y : CxPts p σ'), ρ ≤ P.nu 0 1 σ' y s → P.nu N 0 σ' y f ≤ R) → ∀ y ∈ W, P.nu N 0 σ y f ≤ Real.exp (δ * N) * R := by
  intro k _ X _ p D hX P s hs hs0 δ hδ σ y₀
  set i := pick (P.L.φ σ).isLB y₀
  set j := pick (P.A.φ σ).isLB y₀
  have hyi : y₀ ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ _
  have hyj : y₀ ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ _
  have hxV : y₀.1 (IsLocalRing.closedPoint ℂ) ∈ P.L.B.U i ⊓ P.A.B.U j :=
    GlobalTheory.CxPts.mem_ptsIn.1 (GlobalTheory.CxPts.mem_ptsIn_inf.2 ⟨hyi, hyj⟩)
  obtain ⟨U, hUa, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxV
  have hUi : U ≤ P.L.B.U i := hUV.trans inf_le_left
  have hUj : U ≤ P.A.B.U j := hUV.trans inf_le_right
  have hy₀U : y₀ ∈ ptsIn p σ U := GlobalTheory.CxPts.mem_ptsIn.2 hxU
  have hgen : genericPoint X ∈ U := gen_mem hxU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : CharZero Γ(X, U) := RingHom.charZero (evHom hy₀U)
  have : Algebra.FiniteType ℤ Γ(X, U) := finiteType_int_of_isAffineOpen hX hUa
  let _ : TopologicalSpace (Γ(X, U) →+* ℂ) :=
    TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance
  have hcont : ∀ (M : HermLB p) (c : M.B.ι), U ≤ M.B.U c → ∀ σ' : k →+* ℂ,
      ContinuousOn (fun y => (M.φ σ').φ c y / 2) (ptsIn p σ' U) := by
    intro M c hc σ' y hy
    exact ((M.cInf σ' c y (ptsIn_mono hc hy)).continuousAt.div_const 2).continuousWithinAt
  obtain ⟨ψ, hψc, hψv, hsurj, hnb⟩ :=
    GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms k X p D hX U hUa (fun σ' y => (P.L.φ σ').φ i y / 2) (hcont P.L i hUi)
  obtain ⟨ψ', hψ'c, hψ'v, -, -⟩ :=
    GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms k X p D hX U hUa (fun σ' y => (P.A.φ σ').φ j y / 2) (hcont P.A j hUj)
  have hsreg : ∀ x ∈ U, RegAt x (P.loc 0 1 s i j) := fun x hx => hs x i j (hUi hx) (hUj hx)
  obtain ⟨s', hs'⟩ := exists_fnOf_eq hgen hsreg
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    simp [Pair.loc, hs0] at hs'
  obtain ⟨W', K, hW', hK, hKs, hmain⟩ := GlobalTheory.T.local_max_principle_weighted_finiteType_int Γ(X, U) ψ hψc s' hs'0 (evHom hy₀U) δ hδ
  have hgc : Continuous (fun x : Γ(X, U) →+* ℂ => ‖x s'‖ * Real.exp (-ψ' x)) :=
    (((continuous_apply s').comp continuous_induced_dom).norm).mul (Real.continuous_exp.comp hψ'c.neg)
  obtain ⟨ρ, hρ, hρK⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ρ ≤ ‖x s'‖ * Real.exp (-ψ' x) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨x₁, hx₁, hmin⟩ := hK.exists_isMinOn hKne hgc.continuousOn
      exact ⟨_, mul_pos (norm_pos_iff.2 (hKs x₁ hx₁)) (Real.exp_pos _), fun x hx => isMinOn_iff.mp hmin x hx⟩
  refine ⟨{z | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W'}, ρ, hnb σ y₀ hy₀U W' hW', hρ, ?_⟩
  intro N f R hf hR y hyW
  obtain ⟨hyU, hyW'⟩ := hyW
  have hfreg : ∀ x ∈ U, RegAt x (P.loc N 0 f i j) := fun x hx => hf x i j (hUi hx) (hUj hx)
  obtain ⟨f', hf'⟩ := exists_fnOf_eq hgen hfreg
  have hnuF : ∀ (σ' : k →+* ℂ) (z : CxPts p σ') (hz : z ∈ ptsIn p σ' U),
      P.nu N 0 σ' z f = ‖evHom hz f'‖ * Real.exp (-(N * ψ (evHom hz))) := by
    intro σ' z hz
    rw [GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames k X p P N 0 f hf σ' z i j (ptsIn_mono hUi hz) (ptsIn_mono hUj hz), ← hf',
      ratVal_fnOf hz hgen, ev_eq hz, hψv σ' z hz]
    congr 2
    push_cast
    ring
  have hnuS : ∀ (σ' : k →+* ℂ) (z : CxPts p σ') (hz : z ∈ ptsIn p σ' U),
      P.nu 0 1 σ' z s = ‖evHom hz s'‖ * Real.exp (-ψ' (evHom hz)) := by
    intro σ' z hz
    rw [GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames k X p P 0 1 s hs σ' z i j (ptsIn_mono hUi hz) (ptsIn_mono hUj hz), ← hs',
      ratVal_fnOf hz hgen, ev_eq hz, hψ'v σ' z hz]
    congr 2
    push_cast
    ring
  rw [hnuF σ y hyU]
  refine hmain N f' R ?_ (evHom hyU) hyW'
  intro x hx
  obtain ⟨σ', z, hz, rfl⟩ := hsurj x
  rw [← hnuF σ' z hz]
  exact hR σ' z (by rw [hnuS σ' z hz]; exact hρK _ hx)

end GlobalTheory.VolBr
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.holomorphicType_of_smooth_borelKilled : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ f, SmFn Hm f → KilledFn Hm x₀ w f → HolFn Hm q x₀ w f := by
  first | exact @GlobalTheory.HolDict.holFn_of_killed | exact GlobalTheory.HolDict.holFn_of_killed | (intros; apply GlobalTheory.HolDict.holFn_of_killed <;> assumption)
end

section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

theorem _root_.GlobalTheory.T.unramifiedExtFrobenius_iterate_degree_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∀ x : Kn p K r, (⇑(frobR p K r))^[r] x = x := by
  first | exact @GlobalTheory.LKLoc.frobR_iterate_self | exact GlobalTheory.LKLoc.frobR_iterate_self | (intros; apply GlobalTheory.LKLoc.frobR_iterate_self <;> assumption)
end

section

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out q) = ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G), ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) := by
  first | exact @GlobalTheory.finsum_fold_intermediate | exact GlobalTheory.finsum_fold_intermediate | (intros; apply GlobalTheory.finsum_fold_intermediate <;> assumption)
end

section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU
open GlobalTheory.AdelicSvN GlobalTheory.AdelicSvNLevi

namespace GlobalTheory.TowU.LeviModel

variable {F : Type} [Field F] [NumberField F]

theorem isOp_levi (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : IsUnit A.det) :
    IsOp ψ (AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) (compM A⁻¹) (compM A) := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix ι ι (AF F) := A.map (algebraMap F (AF F))
  let Aim : Matrix ι ι (AF F) := A⁻¹.map (algebraMap F (AF F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine
    { pres := comp_mem A⁻¹ A h2 h1
      pres' := comp_mem A A⁻¹ h1 h2
      left := fun φ _ => funext fun x => ?_
      right := fun φ _ => funext fun x => ?_
      adm := fun l hl g hg => ?_
      adm' := fun l hl g hg => ?_
      Heisenberg₂ := fun w φ _ => funext fun x => ?_
      theta := ⟨1, one_ne_zero, fun φ _ => ?_⟩
      norm := fun μ μ' hμ hμ' => ?_ }
  · change φ (Aim *ᵥ (Am *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  · change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A A⁻¹ h1 h2).continuous,
      hg.2.comp_homeomorph (finHomeo A A⁻¹ h1 h2)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A A⁻¹ h1 h2)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A A⁻¹ h1 h2, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  · rw [one_mul]
    unfold thetaSum
    let e : (ι → F) ≃ (ι → F) :=
      { toFun := fun ξ => A⁻¹ *ᵥ ξ
        invFun := fun ξ => A *ᵥ ξ
        left_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
        right_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] }
    have he := Equiv.tsum_eq e (fun ξ : ι → F => φ fun i => algebraMap F (AF F) (ξ i))
    refine Eq.trans (tsum_congr fun ξ => ?_) he
    change φ (Aim *ᵥ _) = φ (fun i => algebraMap F (AF F) ((A⁻¹ *ᵥ ξ) i))
    congr 1
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) A⁻¹ ξ i).symm
  · haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    letI : MeasurableSpace (ι → AF F) := borel _
    haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
    let L : (ι → AF F) ≃+ (ι → AF F) :=
      { toFun := fun x => Aim *ᵥ x
        invFun := fun x => Am *ᵥ x
        left_inv := fun x => by simp only [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
        right_inv := fun x => by simp only [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
        map_add' := fun x y => Matrix.mulVec_add _ _ _ }
    have hc : Continuous L := continuous_const.matrix_mulVec continuous_id
    have hc' : Continuous L.symm := continuous_const.matrix_mulVec continuous_id
    let H : (ι → AF F) ≃ₜ (ι → AF F) := { toEquiv := L.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
    haveI : (Measure.map L μ').IsAddHaarMeasure := L.isAddHaarMeasure_map μ' hc hc'
    have e := Measure.isAddLeftInvariant_eq_smul (Measure.map L μ') μ
    refine ⟨Measure.addHaarScalarFactor (Measure.map L μ') μ, ?_, ENNReal.coe_ne_top, fun φ _ => ?_⟩
    · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (Measure.map L μ') μ).ne'
    · have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) H.toMeasurableEquiv (μ := μ')
      change ∫⁻ x, ‖φ (Aim *ᵥ x)‖ₑ ^ 2 ∂μ' = _
      have hL : (Measure.map H.toMeasurableEquiv μ') = Measure.map L μ' := rfl
      rw [hL, e, lintegral_smul_measure] at hm
      exact hm.symm.trans rfl

theorem inv_diag {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A 0 0 A)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul A hA]
  simp [Matrix.fromBlocks_one]

theorem dblAct_levi {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : IsUnit A.det) :
    dblAct (AdelicSvN.act (R := AF F) (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) =
      AdelicSvN.act (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 A) 0 0 (Matrix.fromBlocks A 0 0 A)⁻¹ᵀ) := by
  funext w
  rw [inv_diag A hA, act_levi, Matrix.fromBlocks_transpose]
  simp only [dblAct, act_levi, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add, Matrix.transpose_zero, Matrix.mulVec_neg, neg_neg]

theorem isOp2_levi (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : IsUnit A.det) :
    IsOp2 ψ (AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) (compM A⁻¹) (compM A) := by
  have hA2 : IsUnit (Matrix.fromBlocks A 0 0 A).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hA
  refine ⟨isOp_levi ψ A hA, compM (Matrix.fromBlocks A 0 0 A)⁻¹, compM (Matrix.fromBlocks A 0 0 A), ?_,
    fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_levi A hA]; exact isOp_levi ψ _ hA2
  · funext x
    rw [inv_diag A hA]
    change boxFun φ₁ φ₂ _ = φ₁ _ * star (star (φ₂ _))
    rw [star_star]
    simp only [boxFun, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec, add_zero, zero_add]
    rfl

end GlobalTheory.TowU.LeviModel


open GlobalTheory.TowU.LeviModel in
theorem GlobalTheory.TowU.realised_levi2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ A : Matrix κ κ F, IsUnit A.det →
    ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
      IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) S S' :=
  fun _ _ _ ψ _ _ _ _ A hA => ⟨_, _, isOp2_levi ψ A hA⟩

end
end

section

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.mass_mul_volume_commensurable : ∀ {G : Type} [Group G] (Γ' T C C' : Subgroup G), C ≤ T → C' ≤ T → C.relIndex C' ≠ 0 → C'.relIndex C ≠ 0 → (∀ t ∈ T, ((Γ' ⊓ C.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) → (∀ t ∈ T, ((Γ' ⊓ C'.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) → massC Γ' T C' * vol C C' = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.MassChange.massC_mul_vol | exact GlobalTheory.LKCount.MassChange.massC_mul_vol | (intros; apply GlobalTheory.LKCount.MassChange.massC_mul_vol <;> assumption)
end

section

noncomputable section

open MeasureTheory
open Formalism.REAL (KG toMK muK)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF

theorem norm_irreducibleCharacter_unitaryMaxCompact_eq_one : SchurOne := by
  intro n ε γ W _ _ _ T hT
  obtain ⟨hnt, hU, hK⟩ := hT
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  let π : KG ε →* (W →L[ℂ] W) :=
    { toFun := fun k => T (toMK k)
      map_one' := hU.1.1
      map_mul' := fun a b => hU.1.2 _ a.2 _ b.2 }
  have hπU : GlobalTheory.OpTrace.IsUnitaryRep π :=
    ⟨fun k v => hU.2.1 _ k.2 v, fun v => (hU.2.2 v).comp_continuous hemb.continuous fun k => k.2⟩
  have hπI : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π := by
    refine ⟨hnt, fun S hS => ?_⟩
    refine hK.2.2.1 S le_top fun g hg v hv => ?_
    have : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [Formalism.REAL.range_toMK]; exact hg
    obtain ⟨k, rfl⟩ := this
    exact hS.2 k v hv
  have h := GlobalTheory.Orb.integral_conj_trace_mul_trace (μ := muK ε) hπU hπI
  have h1 : (muK ε).real Set.univ = 1 := by
    rw [Measure.real, Formalism.REAL.muK, ← TopologicalSpace.PositiveCompacts.coe_top, Measure.haarMeasure_self]
    rfl
  rw [h1] at h
  exact_mod_cast h

end GlobalTheory.PsCo.PcEF
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.isOpen_offCoordinateHyperplanes : ∀ {n : ℕ} (S : Finset (Fin n)) (U : Set (V n)), IsOpen U → IsOpen (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | exact GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | (intros; apply GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen <;> assumption)
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop


set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.continuousAt_corrC :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ}
      {G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      ContDiffAt ℝ 1 ρ v → _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₀ v → IsUnit (G₀ v).det →
        _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₁ v → IsUnit (G₁ v).det →
        ContinuousAt (_root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁) v := by
  intro n r _ _ ρ G₀ G₁ v hρ h₀ hd₀ h₁ hd₁
  have hcurv : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a b p q, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G x (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) p q) v :=
    fun hG hdG a b p q =>
      (hG.curv (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q).continuousAt
  have hconn : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a p q, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G x (_root_.GlobalTheory.GoodMetric.coordVec a) p q) v :=
    fun hG hdG a p q =>
      (hG.conn (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) p q).continuousAt
  have hposition : ∀ j : Fin n, ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j)) v := by
    intro j
    apply _root_.GlobalTheory.GoodTop.continuousAt_mixTop
    intro i a b p q
    unfold _root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one _root_.GlobalTheory.GoodTop.curvAt _root_.GlobalTheory.GoodTop.cutForm
    split_ifs
    · exact hcurv h₁ hd₁ a b p q
    · exact (continuousAt_dbar_ofReal_of_contDiffAt_one hρ _).mul ((hconn h₁ hd₁ a p q).sub (hconn h₀ hd₀ a p q))
    · exact hcurv h₀ hd₀ a b p q
  have heq : _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ = fun x => ∑ j, _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j) := by
    funext x
    rfl
  rw [heq]
  exact tendsto_finsetSum _ fun j _ => hposition j

end GlobalTheory.GoodTop
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma continuousAt_cutoff_mul_chern_form_coeff {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hG : _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G v) (hdet : IsUnit (G v).det) (hρ : ContinuousAt ρ v) :
    ContinuousAt (fun x => (ρ x : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G x)
      v := by
  refine ContinuousAt.mul (Complex.continuous_ofReal.continuousAt.comp (f := ρ) hρ) ?_
  refine _root_.GlobalTheory.GoodTop.continuousAt_mixTop (K := fun x _ => _root_.GlobalTheory.GoodTop.curvAt G x)
    fun i a b p q => ?_
  have h := hG.curv (j := 0) hdet
    (by rw [zero_add]; first | exact le_top | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤)) | exact WithTop.coe_le_coe.2 le_top)
    (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q
  exact h.continuousAt


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
      IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U →
      (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) U := by
  intro n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ hρK
  have hcont : ContinuousOn
      (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) K :=
    fun v hv => (continuousAt_cutoff_mul_chern_form_coeff (hG₀ v (hKU hv)).1 (hG₀ v (hKU hv)).2
      (hρ.contDiffAt (hU.mem_nhds (hKU hv))).continuousAt).continuousWithinAt
  refine (hcont.integrableOn_compact hK).of_forall_diff_eq_zero hU.measurableSet
    fun v hv => ?_
  rw [hρK v hv.1 hv.2, Complex.ofReal_zero, zero_mul]

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, DifferentiableAt ℝ ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b)) = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | exact GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | (intros; apply GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub <;> assumption)
end
