module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle012
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.V00
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.frame_criterion_projection :
    UpperTheory.V.Pr.CrPi := by
  unfold UpperTheory.V.Pr.CrPi
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS
  have hup : Continuous (toUpl Ω L) := by
    unfold UpperTheory.V.Pr.toUpl
    exact (continuous_restrictScalarsHom ℚ (W.Lp L) Ω).subtype_mk _
  let f : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (toUpl Ω L)
  have hf : Continuous f := k.p_cont.comp hup
  have hclosed : IsClosed (f.ker : Set (G (W.Lp L) Ω)) := by
    have h := (isClosed_singleton (x := (1 : Φ.Γ))).preimage hf
    exact h
  have hNS : NS Ω V.S' ≤ f.ker := by
    unfold ReciprocityTheory.Gal.NS
    apply Subgroup.topologicalClosure_minimal _ _ hclosed
    apply Subgroup.normalClosure_le_normal
    intro t ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at ht
    obtain ⟨v, hv, A, hA, ht⟩ := ht
    rw [hS] at hv
    unfold UpperTheory.V.W.HidaSetting.S at hv
    simp only [Set.mem_setOf_eq, not_or] at hv
    obtain ⟨hl, hSt, -⟩ := hv
    have hMv := fun hM => hSt ((x.St v).2 ⟨hM, hl⟩)
    have hti : galEmb ℚ (W.Lp L) Ω t ∈ Ine A := (galEmb_mem_Ine A t).2 ht
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show k.p (toUpl Ω L t) = 1
    rw [← MonoidHom.mem_ker, k.p_ker]
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    refine ⟨A, ?_, hti, ?_, ?_⟩
    · rw [natCast_place hA]
      exact hl
    · exact k.unr A ⟨hti, (toUpl Ω L t).2⟩
    · have hΨ : Ψ (galEmb ℚ (W.Lp L) Ω t) = 1 :=
        x.unr A (by rw [natCast_place hA]; exact hMv) hti
      unfold barChar
      show Units.map _ (Ψ (galEmb ℚ (W.Lp L) Ω t)) = 1
      rw [hΨ, map_one]
  let πt : GS Ω V.S' →* Φ.Γ := QuotientGroup.lift (NS Ω V.S') f hNS
  have hπt : ∀ t, πt (toGS Ω V.S' t) = f t := fun t => rfl
  have hπtc : Continuous πt := continuous_coinduced_dom.2 hf
  have hmem : ∀ y : V.η.ker, πt y.1 ∈ Φ.del.ker := by
    intro y
    obtain ⟨g, hg⟩ := pr_surj V y
    rw [← hg]
    exact (k.p0 g).2
  let π : V.η.ker →* Φ.del.ker := (πt.comp V.η.ker.subtype).codRestrict _ hmem
  have hcs : f s.c = Φ.c := by
    obtain ⟨h, hpc⟩ := k.c
    have h2 : toUpl Ω L s.c = ⟨σ, h⟩ := Subtype.ext x.c
    show k.p (toUpl Ω L s.c) = Φ.c
    rw [h2, hpc]
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · exact (hπtc.comp continuous_subtype_val).subtype_mk _
  · intro g
    rfl
  · intro y0
    let y : V.η.ker := y0
    apply Subtype.ext
    show πt (toGS Ω V.S' s.c * y.1 * (toGS Ω V.S' s.c)⁻¹) = Φ.c * πt y.1 * Φ.c⁻¹
    rw [map_mul, map_mul, map_inv, hπt, hcs]
  · intro y0
    let y : V.η.ker := y0
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') y.1
    show Φ.eps (πt y.1) = V.ε y.1
    have ht' : toGS Ω V.S' t = y.1 := ht
    rw [← ht', hπt]
    show Φ.eps (k.p (toUpl Ω L t)) = V.ε (toGS Ω V.S' t)
    rw [k.eps, ← MonoidHom.comp_apply V.ε, V.hε]
    rfl
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr

end UpperTheory.V.Pr

theorem UpperTheory.frame_criterion_residual :
    UpperTheory.V.Pr.CrResid := by
  intro l _ O _ _ _ F G n hn hk hg π hπ hs hc κ hκ hκe
  let χ : Fin n → G.G₀ →* (ResidueField O)ˣ := fun i =>
    { toFun := fun g => F.Ψ (π g : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ g
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [map_mul, Subgroup.coe_mul, mul_zpow]
        exact mul_mul_mul_comm _ _ _ _ }
  have hψ : IsOpen ((F.Ψ.comp (F.del.ker.subtype.comp π)).ker : Set G.G₀) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact hk.preimage (continuous_subtype_val.comp hπ)
  have hκo : IsOpen ((W.pushCh (residue O) κ).ker : Set G.G₀) := by
    have h1 := (hκ 1).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal O ^ 1) 1)
    convert h1 using 1
    ext g
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, Ideal.Quotient.eq, pow_one, Units.ext_iff]
    show residue O (κ g : O) = 1 ↔ _
    rw [← map_one (residue O)]
    exact Ideal.Quotient.eq
  have hopen : ∀ i, IsOpen ((χ i).ker : Set G.G₀) := by
    intro i
    refine Subgroup.isOpen_mono (H₁ := (F.Ψ.comp (F.del.ker.subtype.comp π)).ker ⊓ (W.pushCh (residue O) κ).ker) ?_ (by rw [Subgroup.coe_inf]; exact hψ.inter hκo)
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker]
    show F.Ψ (π g : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ g = 1
    rw [hg.2, mul_one]
    have : F.Ψ (π g : F.Γ) = 1 := hg.1
    rw [this, one_zpow]
  have hinj : Function.Injective χ := by
    intro i j hij
    obtain ⟨g, hg0⟩ := hs F.g0
    have h := DFunLike.congr_fun hij g
    change F.Ψ (π g : F.Γ) ^ Fr.w n i * _ = F.Ψ (π g : F.Γ) ^ Fr.w n j * _ at h
    rw [mul_right_cancel_iff, hg0] at h
    have key : F.Ψ (F.g0 : F.Γ) ^ (Fr.w n i - Fr.w n j) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    have hu2 : F.Ψ (F.g0 : F.Γ) ^ (2:ℤ) ≠ 1 := by exact_mod_cast hg
    have hu1 : F.Ψ (F.g0 : F.Γ) ≠ 1 := by
      intro h1
      apply hu2
      rw [h1, one_zpow]
    rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [Fr.w] at key ⊢
    all_goals first
      | exact hg key
      | exact hu1 key
      | exact hu2 key
      | exact hu1 (inv_eq_one.mp key)
      | exact hg (inv_eq_one.mp (by simpa [zpow_neg] using key))
  have hw : ∀ i : Fin n, Fr.w n (Fin.rev i) = - Fr.w n i := by
    intro i
    rcases hn with rfl | rfl <;> fin_cases i <;> simp [Fr.w] <;> decide
  have hΨc : ∀ g, F.Ψ (π (G.conj g) : F.Γ) = F.Ψ (π g : F.Γ) := by
    intro g
    rw [hc]
    simp [Fr.Frame.conj, MulAut.conjNormal_apply]
  have heps : ∀ g, Units.map (residue O : O →* ResidueField O) (G.eps O O g) = G.eps O (ResidueField O) g := by
    intro g
    ext
    simp [W.GFrame.eps, W.pushCh]
  have hκc : ∀ g, W.pushCh (residue O) κ (G.conj g) = (G.eps O (ResidueField O) g) ^ (1 - (n:ℤ)) * (W.pushCh (residue O) κ g)⁻¹ := by
    intro g
    have h1 : κ (G.conj g) = (G.eps O O g) ^ (1 - (n:ℤ)) * (κ g)⁻¹ := by
      rw [← hκe g, mul_comm (κ g) (κ (G.conj g)), mul_inv_cancel_right]
    show Units.map (residue O : O →* ResidueField O) (κ (G.conj g)) = _
    rw [h1, map_mul, map_inv, map_zpow, heps]
    rfl
  have hstar : ∀ i g, (G.eps O (ResidueField O) g) ^ (1 - (n:ℤ)) * (χ i (G.conj g))⁻¹ = χ (Fin.rev i) g := by
    intro i g
    show _ * (F.Ψ (π (G.conj g) : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ (G.conj g))⁻¹ = F.Ψ (π g : F.Γ) ^ Fr.w n (Fin.rev i) * W.pushCh (residue O) κ g
    rw [hΨc, hκc, hw, zpow_neg, mul_inv, mul_inv, inv_inv, mul_left_comm, mul_inv_cancel_left]
  have hpolar : G.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
    intro B _ _ _ _ y
    let f : Fin n → G.G₀ →* B := fun i => (algebraMap (ResidueField O) B : ResidueField O →* B).comp ((Units.coeHom (ResidueField O)).comp (χ i))
    have hdiag : ∀ z : MonoidAlgebra B G.G₀, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => MonoidAlgebra.lift B B G.G₀ (f i) z) := by
      intro z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy =>
        rw [map_add (f := _), hx, hy, Matrix.diagonal_add]
        congr 1
        ext i
        simp [map_add (f := _)]
      | single g b =>
        ext i j
        simp [f, W.GDet.repAlg, W.diagRep, MonoidAlgebra.lift_single, Matrix.diagonal_apply]
    have hepsB : ∀ g, Units.map (algebraMap (ResidueField O) B : ResidueField O →* B) (G.eps O (ResidueField O) g) = G.eps O B g := by
      intro g
      ext
      simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O (ResidueField O) B]
    have hs1 : ∀ (g : G.G₀) (b : B), G.star O B n (MonoidAlgebra.single g b) = MonoidAlgebra.single (G.conj g)⁻¹ (b * ((G.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B)) := by
      intro g b
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single']
    have hrev : ∀ i z, MonoidAlgebra.lift B B G.G₀ (f i) (G.star O B n z) = MonoidAlgebra.lift B B G.G₀ (f (Fin.rev i)) z := by
      intro i z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp [W.GFrame.star]
      | add x y hx hy =>
        have hadd : G.star O B n (x + y) = G.star O B n x + G.star O B n y := by simp [W.GFrame.star]
        rw [hadd, map_add (f := _), map_add (f := _), hx, hy]
      | single g b =>
        rw [hs1 g b, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single, smul_eq_mul, smul_eq_mul, mul_assoc]
        congr 1
        rw [← hepsB g, ← map_zpow, Units.coe_map]
        show _ = algebraMap (ResidueField O) B ((χ (Fin.rev i) g : (ResidueField O)ˣ) : ResidueField O)
        rw [← hstar i g, Units.val_mul, map_mul]
        simp [f]
    show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (G.star O B n y)) = Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
    rw [hdiag, hdiag, Matrix.det_diagonal, Matrix.det_diagonal]
    simp only [hrev]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)
  refine ⟨⟨χ, hopen, hinj, hpolar, fun v i => (χ i).comp (G.φ v), ?_, fun _ _ => 1, ?_⟩, ?_, ?_⟩
  · intro v i
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (hopen i).preimage (G.φ_cont v)
  · intro v i g _
    rfl
  · intro i g
    rfl
  · intro v i g
    rfl
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

private theorem open_toZMod (l : ℕ) [Fact l.Prime] : IsOpen {x : ℤ_[l] | PadicInt.toZMod x = 1} := by
  have hS : {x : ℤ_[l] | PadicInt.toZMod x = 1} = {x | ‖x - 1‖ < 1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod,
      RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
  rw [hS]
  exact isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem UpperTheory.frame_criterion_decomposition_groups :
    UpperTheory.V.Pr.ExistsPrimeSplitInKernelWithNontrivialCyclotomic := by
  unfold UpperTheory.V.Pr.ExistsPrimeSplitInKernelWithNontrivialCyclotomic
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k hK g hg hc M' hM'
  let ρ : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (toUpl Ω L)
  have hemb : Continuous (galEmb ℚ (W.Lp L) Ω) := (galEmbTop ℚ (W.Lp L) Ω).1.continuous
  have hρ : Continuous ρ := by
    have hto : Continuous (toUpl Ω L) := continuous_induced_rng.2 hemb
    exact k.p_cont.comp hto
  let U1 : Subgroup (G (W.Lp L) Ω) := Φ.Ψ.ker.comap ρ
  let U2 : Subgroup (G (W.Lp L) Ω) :=
    ((Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom).comp (cycZ (W.Lp L) Ω l)).ker
  let U3 : Subgroup (G (W.Lp L) Ω) := (η.comp (galEmb ℚ (W.Lp L) Ω)).ker
  have hU2 : ∀ τ, τ ∈ U2 ↔ PadicInt.toZMod (cycZ (W.Lp L) Ω l τ : ℤ_[l]) = 1 := by
    intro τ
    simp [U2, MonoidHom.mem_ker, Units.ext_iff]
  have hfix : ∀ τ : G (W.Lp L) Ω, τ ∈ galOf (W.Lp L) L Ω ↔ τ ∈ U3 := by
    intro τ
    change _ ↔ η (galEmb ℚ (W.Lp L) Ω τ) = 1
    rw [← k.mem_range_resP τ, mem_galOf]
    constructor
    · intro hτ
      exact ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), AlgEquiv.ext fun y => rfl⟩
    · rintro ⟨t, rfl⟩ x
      exact t.commutes x
  have hO1 : IsOpen (U1 : Set (G (W.Lp L) Ω)) := hK.preimage hρ
  have hO2 : IsOpen (U2 : Set (G (W.Lp L) Ω)) := by
    have hset : (U2 : Set (G (W.Lp L) Ω)) =
        (fun τ => (cycZ (W.Lp L) Ω l τ : ℤ_[l])) ⁻¹' {x : ℤ_[l] | PadicInt.toZMod x = 1} := by
      ext τ
      exact hU2 τ
    rw [hset]
    exact (open_toZMod l).preimage (Units.continuous_val.comp (continuous_cycZ (W.Lp L) Ω l))
  have hO3 : IsOpen (U3 : Set (G (W.Lp L) Ω)) := by
    have hset : (U3 : Set (G (W.Lp L) Ω)) = galOf (W.Lp L) L Ω := by
      ext τ
      exact (hfix τ).symm
    rw [hset]
    exact (galEmbTop (W.Lp L) L Ω).2.1
  haveI hN1 : U1.Normal := (Φ.Ψ.normal_ker).comap ρ
  let U : Subgroup (G (W.Lp L) Ω) := U1 ⊓ U2 ⊓ U3
  haveI : U.Normal := inferInstance
  have hOU : IsOpen (U : Set (G (W.Lp L) Ω)) := (hO1.inter hO2).inter hO3
  let g' : G (W.Lp L) Ω := W.resP L Ω g
  obtain ⟨w, A, p, σ', -, hp, hpM, -, hpw, hnorm, -, hA, hIne, hFrob, hσU⟩ :=
    Loc.v00 U hOU g' ∅ M' hM'
  have hg'1 : g' ∈ U1 := hg
  have hg'3 : g' ∈ U3 := (k.mem_range_resP g').1 ⟨g, rfl⟩
  have hσeq : σ' = g' * (σ'⁻¹ * g')⁻¹ := by group
  have hσ1 : σ' ∈ U1 := by
    rw [hσeq]
    exact U1.mul_mem hg'1 (U1.inv_mem hσU.1.1)
  have hσ3 : σ' ∈ U3 := by
    rw [hσeq]
    exact U3.mul_mem hg'3 (U3.inv_mem hσU.2)
  have hσ2 : σ' ∉ U2 := by
    intro h
    have h2 := U2.mul_mem h hσU.1.2
    rw [mul_inv_cancel_left] at h2
    exact hc ((hU2 g').1 h2)
  let H : Subgroup (G (W.Lp L) Ω) := U1 ⊓ U3
  have hOH : IsOpen (H : Set (G (W.Lp L) Ω)) := hO1.inter hO3
  have hIH : Ine A ≤ H := fun τ hτ => ⟨(hIne hτ).1.1, (hIne hτ).2⟩
  have hFrob' : IsFrob A (normV w) σ' := by
    rw [hnorm]
    exact hFrob
  have hDec : (Dec A : Subgroup (G (W.Lp L) Ω)) ≤ H :=
    Kum.decGen (W.Lp L) Ω A w σ' H hA hFrob' hOH hIH ⟨hσ1, hσ3⟩
  refine ⟨w, A, p, hp, hpM, hnorm, hpw, hA, ?_, ?_, ?_⟩
  · intro τ hτ
    exact (k.mem_range_resP τ).2 (hDec hτ).2
  · intro t ht
    have ht' : W.resP L Ω t ∈ (Dec A : Subgroup (G (W.Lp L) Ω)) := ht
    exact (hDec ht').1
  · obtain ⟨t, ht⟩ := (k.mem_range_resP σ').2 hσ3
    refine ⟨t, ?_, ?_⟩
    · change W.resP L Ω t ∈ (Dec A : Subgroup (G (W.Lp L) Ω))
      rw [ht]
      exact hFrob.1
    · change PadicInt.toZMod (cycZ (W.Lp L) Ω l (W.resP L Ω t) : ℤ_[l]) ≠ 1
      rw [ht]
      exact fun h => hσ2 ((hU2 σ').2 h)
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

open scoped Pointwise in
private theorem val_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (g : G F Ω) (A : ValuationSubring Ω) (x : Ω) :
    (g • A).valuation (g x) < 1 ↔ A.valuation x < 1 := by
  have key : ∀ y : Ω, g.toRingEquiv y ∈ g • A ↔ y ∈ A := by
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists _ _ _).1 hy
      have hzy' : g z = g y := hzy
      rw [g.injective hzy'] at hz
      exact hz
    · intro hy
      exact ValuationSubring.smul_mem_pointwise_smul g y A hy
  exact val_lt_one key x

open scoped Pointwise in
private theorem place_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (g : G F Ω) {A : ValuationSubring Ω}
    {v : W.Plc F} (h : IsPlaceOver A v) : IsPlaceOver (g • A) v := by
  intro x
  have hx : g ((algebraMap F Ω) (x : F)) = (algebraMap F Ω) (x : F) := g.commutes _
  rw [← hx, val_smul]
  exact h x

open scoped Pointwise in
theorem UpperTheory.frame_criterion_galois_equivariance :
    UpperTheory.V.Pr.CrE := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k hB
  have hsm : ∀ (τ : G (W.Lp L) Ω) (X : ValuationSubring Ω),
      τ • X = ((toUpl Ω L τ : upl Ω L) : Gal(Ω/ℚ)) • X := by
    intro τ X
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : ((toUpl Ω L τ : upl Ω L) : Gal(Ω/ℚ))⁻¹ = ((toUpl Ω L τ⁻¹ : upl Ω L) : Gal(Ω/ℚ)) := by
      rw [map_inv]
      rfl
    rw [hinv]
    rfl
  have hpl : ∀ w : Φ.V, (k.pl w).valuation (l : Ω) < 1 := by
    intro w
    obtain ⟨γ, -, hγ⟩ := k.pl_conj w
    have h1 := (val_smul γ B (l : Ω)).2 hB
    rw [map_natCast] at h1
    rw [hγ]
    exact h1
  have hpick : ∀ v : W.Vl l L, ∃ w : Φ.V, IsPlaceOver (k.pl w) (v : W.Plc (W.Lp L)) := by
    intro v
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω (v : W.Plc (W.Lp L))
    have hlA : A.valuation (l : Ω) < 1 := by
      rw [natCast_place hA]
      exact v.2
    obtain ⟨w, ⟨u, hu, hAu⟩, -⟩ := k.pl_all A hlA
    obtain ⟨g, hg⟩ := toUpl_surj (Ω := Ω) (L := L) (⟨u, hu⟩⁻¹)
    refine ⟨w, ?_⟩
    have heq : g • A = k.pl w := by
      rw [hsm, hg, hAu]
      change u⁻¹ • u • k.pl w = k.pl w
      rw [inv_smul_smul]
    rw [← heq]
    exact place_smul g hA
  choose e he using hpick
  have hinj : Function.Injective e := by
    intro v v' hvv
    have h2 := he v'
    rw [← hvv] at h2
    exact Subtype.ext (eq_of_isPlaceOver (he v) h2)
  have hsurj : Function.Surjective e := by
    intro w
    have hfacts := places (W.Lp L) Ω l (k.pl w)
    have hne : k.pl w ≠ ⊤ := by
      intro htop
      exact (hfacts.2.1 htop).2 (hpl w)
    obtain ⟨v0, hv0⟩ := hfacts.1 hne
    have hl0 : ((l : 𝓞 (W.Lp L))) ∈ v0.asIdeal := (natCast_place hv0 l).1 (hpl w)
    let v : W.Vl l L := ⟨v0, hl0⟩
    refine ⟨v, ?_⟩
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (he v) hv0
    obtain ⟨w', -, huniq⟩ := k.pl_all (k.pl w) (hpl w)
    have hw : w = w' := huniq w ⟨1, one_mem _, (one_smul _ _).symm⟩
    have hev : e v = w' := huniq (e v) ⟨_, (toUpl Ω L τ).2, by rw [← hsm, hτ]⟩
    rw [hw, hev]
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, he⟩
end
