module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle716
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLocallyConstantDOneEqCocycleOfTameInertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KillLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle015
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem lv_gen (hP : Loc.LocalPublishedTheorems) {v l : ℕ} [Fact v.Prime] [Fact l.Prime] (hvl : v ≠ l) {H : Type} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* Formalism.BasicNotions.Loc.GQ v) (hφ : Topology.IsOpenEmbedding φ)
    (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (κ : H →* kˣ) (hκ : IsOpen (κ.ker : Set H))
    (σ : H) (h1 : κ σ ≠ 1) (h2 : Loc.cycA v l k (φ σ) = 1) (z : H → k) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + (κ g : k) * z h) : ∃ m, ∀ g, z g = (κ g : k) * m - m := by
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  have h1' : (κ σ : k) ≠ 1 := fun h => h1 (Units.ext h)
  have hρ : ∀ g x, Loc.chRep κ g x = (κ g : k) * x := fun _ _ => rfl
  have hlc : IsLocallyConstant κ := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' (κ.ker : Set H),
      hκ.preimage (continuous_const.mul continuous_id), by simp, fun h hh => ?_⟩
    have : κ (g⁻¹ * h) = 1 := hh
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have hca : ContAction (Loc.chRep κ) := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro y
    exact (hlc.comp fun u : kˣ => (u : k) * y).continuous
  obtain ⟨f1, f2, e1, e2⟩ := Loc.tateFin hP φ hφ k k (Loc.chRep κ) hca
  have z0 : H0 (Loc.chRep κ) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm σ
    rw [hρ] at this
    rw [Submodule.mem_bot]
    by_contra h
    exact h1' (mul_right_cancel₀ h (by rw [this, one_mul]))
  have z2 : Loc.H0dual ((Loc.cycA v l k).comp φ) (Loc.chRep κ) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    have := hf σ x
    rw [MonoidHom.comp_apply, h2, hρ, ← smul_eq_mul, map_smul, smul_eq_mul, Units.val_one] at this
    by_contra h
    exact h1' (mul_right_cancel₀ h this)
  rw [e2, z0, z2, if_neg hvl, finrank_bot, finrank_bot] at e1
  haveI : Subsingleton (H1 (Loc.chRep κ)) := Module.finrank_zero_iff.1 e1
  have hz1 : z ∈ Z1 (Loc.chRep κ) := ⟨hz.continuous, hc⟩
  have : (Submodule.Quotient.mk ⟨z, hz1⟩ : H1 (Loc.chRep κ)) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at this
  exact this

private theorem lv_dec (hP : Loc.LocalPublishedTheorems) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v l : ℕ} (hv : v.Prime)
    [Fact l.Prime] (hvl : v ≠ l) (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1)
    (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (κ : Dec (F := ℚ) A →* kˣ)
    (hκ : IsOpen (κ.ker : Set (Dec (F := ℚ) A))) (σ : Dec (F := ℚ) A) (h1 : κ σ ≠ 1)
    (h2 : algebraMap ℤ_[l] k (cycZ ℚ Ω l σ : ℤ_[l]ˣ) = 1) (z : Dec (F := ℚ) A → k) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + (κ g : k) * z h) : ∃ m, ∀ g, z g = (κ g : k) * m - m := by
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 A w hAw hw
  obtain ⟨φ, hφ, -, -, -, hcyc, -⟩ := ((Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).2 j).2
  refine lv_gen hP hvl φ hφ k κ hκ σ h1 (Units.ext ?_) z hz hc
  rw [← hcyc l σ] at h2
  exact h2

private theorem lv_red {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (red : O →+* k)
    (hred : ∀ a ∈ maximalIdeal O, red a = 0) (a b : O) : red a = red b ↔ residue O a = residue O b := by
  rw [← sub_eq_zero, ← map_sub, ← sub_eq_zero (a := residue O a), ← map_sub, residue_eq_zero_iff]
  refine ⟨fun h => ?_, hred _⟩
  by_contra hn
  exact ((IsLocalRing.notMem_maximalIdeal.1 hn).map red).ne_zero h

theorem UpperTheory.V.GradeZeroInterpolatingElement.locVanP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → ∀ (k : Type) [Field k] [Finite k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ p ∈ D.Sb, ∀ z : D.Gp p → k, IsLocallyConstant z → (∀ g h : D.Gp p, z (g * h) = z g + red (γ g : c.O) * z h) → ∃ m, ∀ g : D.Gp p, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD hP k _ _ red hred γ hγ p hp z hz hc
  obtain ⟨f1, f2, -, -, -, -, -, -, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hpp, hpl, -, -⟩ := f1 p hp
  obtain ⟨hσ, hom, hne⟩ := f2 p (Finset.mem_insert_of_mem hp)
  have hl : l.Prime := Fact.out
  obtain ⟨i, j, hij, hγ'⟩ : ∃ i j, lamW i ≠ lamW j ∧ ∀ g, γ g * D.ps j g = D.ps i g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 3, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨1, 2, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
    · exact ⟨0, 3, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨3, 2, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨2, 1, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
    · exact ⟨3, 0, by decide, fun g => by simp [Raw.ps]⟩
  have hγr : ∀ g, red (γ g : c.O) * red (D.ps j g : c.O) = red (D.ps i g : c.O) := fun g => by
    rw [← map_mul, ← Units.val_mul, hγ']
  letI : Algebra ℤ_[l] k := (red.comp (algebraMap ℤ_[l] c.O)).toAlgebra
  have hl0 : (l : k) = 0 := by
    have hloc := (dvrFacts l c.O).2.2.1
    have hm : (l : c.O) ∈ maximalIdeal c.O := by
      rw [mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O), isUnit_map_iff]
      exact PadicInt.p_nonunit
    simpa using hred _ hm
  haveI : CharP k l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  let κ : D.Gp p →* kˣ := ((Units.map red.toMonoidHom).comp γ).comp (D.Gp p).subtype
  have hκ : ∀ g : D.Gp p, (κ g : k) = red (γ g : c.O) := fun _ => rfl
  have hker : D.rbar.ker.comap (D.Gp p).subtype ≤ κ.ker := by
    intro g hg
    have hg' : D.rbar g = 1 := hg
    have h1 : ∀ a, red (D.ps a g : c.O) = 1 := fun a => by
      rw [← map_one red, lv_red red hred, map_one]
      have := congrFun (congrFun hg' a) a
      simpa [Raw.rbar, Raw.r0, diagRep] using this
    refine Units.ext ?_
    have := hγr g
    rw [h1, h1, mul_one] at this
    exact this
  refine lv_dec hP hpp hpl (D.pl p) (hD.pl_over p hpp) k κ
    (Subgroup.isOpen_mono hker (fo.preimage continuous_subtype_val)) ⟨D.sg p, hσ⟩ (fun h => ?_) ?_ z hz hc
  · have h' : red (γ (D.sg p) : c.O) = 1 := congrArg Units.val h
    have := hγr (D.sg p)
    rw [h', one_mul, lv_red red hred] at this
    exact hne i j hij this.symm
  · have : red (chiO ℚ Ω l c.O (D.sg p) : c.O) = red 1 := by
      rw [lv_red red hred, map_one]
      exact (hD.om_bar _).symm.trans hom
    rw [map_one] at this
    exact this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem dec_unr {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v : ℕ} (hv : v.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1) :
    (∃ fr : Dec (F := ℚ) A,
      ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤) ∧
    ∀ m : ℕ, m ≠ 0 → ∃ U : Subgroup (Dec (F := ℚ) A), IsOpen (U : Set (Dec (F := ℚ) A)) ∧
      (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ≤ U ∧ U.index = m := by
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 A w hAw hw
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := Loc.iotaFacts (Ω := Ω) j
  have hmem : ∀ g, Loc.iota j g ∈ Dec (F := ℚ) (Loc.placeJ j) := fun g => h2 ▸ ⟨g, rfl⟩
  let f := (Loc.iota j).codRestrict (Dec (F := ℚ) (Loc.placeJ j)) hmem
  have hf : Topology.IsEmbedding f := h1.codRestrict _ hmem
  have hs : Function.Surjective f := fun g => by
    have : (g : G ℚ Ω) ∈ (Loc.iota j).range := by rw [h2]; exact g.2
    obtain ⟨s, hs⟩ := this
    exact ⟨s, Subtype.ext hs⟩
  let e := MulEquiv.ofBijective f ⟨hf.injective, hs⟩
  have hec' : Continuous e.symm := by
    rw [hf.isInducing.continuous_iff]
    have : (f ∘ e.symm) = id := funext fun g => e.apply_symm_apply g
    rw [this]
    exact continuous_id
  have hI : ∀ s, ((e s : ↥(Dec (F := ℚ) (Loc.placeJ j))) : G ℚ Ω) ∈ Ine (F := ℚ) (Loc.placeJ j) ↔ s ∈ Loc.Iq v :=
    fun s => by rw [← h3]; exact Iff.rfl
  obtain ⟨-, -, -, ⟨σ, hσ⟩, -⟩ := Loc.iqBasic v
  refine ⟨⟨f σ, ?_⟩, fun m hm => ?_⟩
  · have h := hs.denseRange.topologicalClosure_map_subgroup hf.continuous (Loc.frobDense σ hσ)
    rw [eq_top_iff, ← h]
    refine Subgroup.topologicalClosure_mono ?_
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨s, hs', rfl⟩
    exact (hI s).2 hs'
  · haveI : NeZero m := ⟨hm⟩
    letI : TopologicalSpace (Multiplicative (ZMod m)) := ⊥
    haveI : DiscreteTopology (Multiplicative (ZMod m)) := ⟨rfl⟩
    obtain ⟨u, u1, u2, u3⟩ := Loc.frobFree σ hσ (Multiplicative (ZMod m)) (Multiplicative.ofAdd 1)
    have hu : Function.Surjective (u.comp e.symm.toMonoidHom) := fun y => by
      refine ⟨e (σ ^ (Multiplicative.toAdd y).val), ?_⟩
      simp [u3, ← ofAdd_nsmul]
    refine ⟨(u.comp e.symm.toMonoidHom).ker, ?_, fun g hg => ?_, ?_⟩
    · exact (isOpen_discrete {1}).preimage (u1.comp hec')
    · refine u2 _ ((hI _).1 ?_)
      have : e (e.symm.toMonoidHom g) = g := e.apply_symm_apply g
      rw [this]
      exact hg
    · rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hu]
      simp

private theorem norm_diag (O R : Type) [CommRing O] [CommRing R] [Algebra O R] {Γ : Type} [Group Γ] (ρ : Γ →* M4 R)
    (d : Γ → Fin 4 → R) (hρ : ∀ g, ρ g = Matrix.diagonal (d g)) (hd : ∀ g, d g 0 * d g 3 = d g 1 * d g 2) :
    (form O).Normalises ρ := by
  refine ⟨fun g => ⟨d g 0 * d g 3, ?_⟩, ⟨1, fun _ _ _ _ => rfl⟩, fun g a b h => ?_⟩
  · have hJ : (form O).JR R = J4 R := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [FormData.JR, form, J4]
    have := hd g
    rw [hJ, hρ, Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [J4] <;> first | linear_combination -this | ring
  · rw [hρ, Matrix.diagonal_apply_ne]
    rintro rfl
    exact h rfl

private theorem loc_diag (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (h2 : IsUnit (2 : O))
    (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [T2Space Γ] (χ : Fin 4 → Γ →* Oˣ) (hχ : χ 0 * χ 3 = χ 1 * χ 2) (rbar : Γ →* M4 (ResidueField O))
    (r0 : Lift O rbar O) (h0 : r0.hom = diagRep χ) (hop : IsOpen (rbar.ker : Set Γ)) (I : Subgroup Γ) [I.Normal]
    (hI : IsClosed (I : Set Γ)) (hfr : ∃ fr : Γ, (I ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤)
    (hU : ∀ n : ℕ, ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ I ≤ U ∧ U.index = l ^ n)
    (hN : ∀ n ∈ I ⊓ rbar.ker, r0.hom n = 1) :
    (form O).IsLocCond r0.hom (I ⊓ rbar.ker) (killCond rbar (I ⊓ rbar.ker : Subgroup Γ)) := by
  have hχ' : ∀ g, (χ 0 g : O) * χ 3 g = χ 1 g * χ 2 g := fun g => by
    simpa using congrArg (fun φ : Γ →* Oˣ => (φ g : O)) hχ
  have hrb : ∀ g, rbar g = Matrix.diagonal fun i => residue O (χ i g) := fun g => by
    ext a b
    have e : ∀ x : O, res O O x = residue O x := fun x => (res O O).commutes x
    rw [← r0.red, e, h0]
    show residue O (Matrix.diagonal (fun i => (χ i g : O)) a b) = _
    simp only [Matrix.diagonal_apply]
    split_ifs <;> simp
  have hbar : (form O).Normalises rbar := norm_diag O _ rbar _ hrb fun g => by
    simp only [← map_mul, hχ']
  refine kill_loc O _ _ _ (form O) h2 Γ rbar r0 hbar
    (norm_diag O O _ (fun g i => (χ i g : O)) (fun g => by rw [h0]; rfl) hχ') _ hN fun j => ?_
  have hk : rbar.ker ≤ (FormData.adRep hbar j).ker := fun g hg => by
    have h1 : rbar g = 1 := hg
    have h3 : rbar g⁻¹ = 1 := inv_mem hg
    refine LinearMap.ext fun Y => Subtype.ext ?_
    show rbar g * Y.1 * rbar g⁻¹ = Y.1
    rw [h1, h3, one_mul, mul_one]
  refine exists_locallyConstant_dOne_eq_cocycle_of_tame_inertia l (ResidueField O) Γ _ (FormData.adRep hbar j) (Subgroup.isOpen_mono hk hop) I _ hI
    (hI.inter (rbar.ker.isClosed_of_isOpen hop)) inf_le_left (inf_le_right.trans hk) ?_ hfr hU
  let t : Γ →* (Fin 4 → (ResidueField O)ˣ) :=
    Pi.monoidHom fun i => (Units.map (residue O : O →* ResidueField O)).comp (χ i)
  have ht : rbar.ker = t.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hrb, ← Matrix.diagonal_one, Matrix.diagonal_injective.eq_iff]
    exact ⟨fun h => funext fun i => Units.ext (congrFun h i), fun h => funext fun i => congrArg Units.val (congrFun h i)⟩
  rw [Subgroup.inf_relIndex_left, ht, Subgroup.relIndex_ker]
  intro hd
  have h4 := hd.trans (Subgroup.card_subgroup_dvd_card (I.map t))
  rw [Nat.card_fun, Nat.card_units] at h4
  have h5 := hl.out.dvd_of_dvd_pow h4
  haveI := Fintype.ofFinite (ResidueField O)
  obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField O) l
  have h6 : l ∣ Nat.card (ResidueField O) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self l n.ne_zero
  have h7 : 1 ≤ Nat.card (ResidueField O) := Nat.card_pos
  exact hl.out.not_dvd_one (Nat.sub_sub_self h7 ▸ Nat.dvd_sub h6 h5)

theorem UpperTheory.V.GradeZeroInterpolatingElement.locCondQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (rb : D.Gam →* M4 (ResidueField c.O)) (r0 : Lift c.O rb c.O), rb.comp (toGS Ω D.SP) = D.rbar → r0.hom.comp (toGS Ω D.SP) = D.r0 → ∀ q : D.frame.Q, (form c.O).IsLocCond (r0.hom.comp (D.frame.ψ q)) (D.frame.N q) (killCond (rb.comp (D.frame.ψ q)) (D.frame.N q)) := by
  intro Ω _ _ _ l hl c D hD rb r0 hrb hr0 ⟨q, hq⟩
  obtain ⟨hqS, hqT⟩ := Finset.mem_sdiff.1 hq
  have hqp := hD.S_prime q hqS
  have hA := hD.pl_over q hqp
  obtain ⟨f1, -, f3, -, -, f6, -, -, -, -, -, f12, -⟩ := facts D hD
  obtain ⟨-, hfin, hlm, -⟩ := abelian₂.dvr_finite l c.O
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  have h2 : IsUnit (2 : c.O) := by
    obtain ⟨-, -, -, -, -, -, -, -, h⟩ := dvrFacts l c.O
    exact_mod_cast h 2 fun hd => hD.l_odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 hd)
  haveI : IsGalois ℚ Ω := {}
  haveI : CompactSpace (D.Gp q) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
  obtain ⟨hfr, hU⟩ := dec_unr hqp (D.pl q) hA
  have e1 : rb.comp (locHom D.SP (D.pl q)) = D.rbar.comp (D.Gp q).subtype := by rw [← hrb]; rfl
  have e2 : r0.hom.comp (locHom D.SP (D.pl q)) = D.r0.comp (D.Gp q).subtype := by rw [← hr0]; rfl
  have e3 : (D.Ip q ⊓ D.rbar.ker).subgroupOf (D.Gp q) =
      (D.Ip q).subgroupOf (D.Gp q) ⊓ (rb.comp (locHom D.SP (D.pl q))).ker := by
    rw [e1]; rfl
  have hAw : Raw.Away D.T (D.pl q) := fun p hp hv => by
    have hpp : p.Prime := by
      rcases Finset.mem_insert.1 hp with rfl | h
      · exact hl.out
      · exact (f1 p h).1
    have hc : IsCoprime (p : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hpp hqp).2 fun h => hqT (h ▸ hp))
    obtain ⟨a, b, hab⟩ := hc
    have hi : ∀ n : ℤ, (D.pl q).valuation (n : Ω) ≤ 1 := fun n =>
      ((D.pl q).valuation_le_one_iff _).mpr (intCast_mem _ n)
    have h1 : (D.pl q).valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi a)) hv
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi b)) hA
    have h3 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    rw [h3, map_one] at h1
    exact lt_irrefl _ h1
  have key := loc_diag l c.O h2 (D.Gp q) (fun i => (D.ps i).comp (D.Gp q).subtype)
    (by
      have := (f6 0).trans (f6 1).symm
      exact congrArg (fun φ => MonoidHom.comp φ (D.Gp q).subtype) this)
    (rb.comp (locHom D.SP (D.pl q))) (r0.comap _ (continuous_locHom D.SP (D.pl q))) e2
    (by rw [e1]; exact f12.preimage continuous_subtype_val) ((D.Ip q).subgroupOf (D.Gp q))
    ((isClosed_Ine _).preimage continuous_subtype_val) hfr (fun n => hU _ (pow_ne_zero n hl.out.ne_zero))
    (by
      rw [← e3]
      intro n hn
      have h1 : ∀ i, D.ps i n = 1 := fun i => f3 i _ hAw _ hn.1 hn.2
      refine (DFunLike.congr_fun e2 n).trans ?_
      show Matrix.diagonal (fun i => (D.ps i n : c.O)) = 1
      simp [h1])
  rw [← e3] at key
  exact key
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Diag

variable {R : Type} [CommRing R]

private theorem prj_diag (c : Fin 4 → R) (i : Fin 4) :
    prj c (Matrix.diagonal c) i = Matrix.diagonal fun a => ∏ j ∈ Finset.univ.erase i, (c a - c j) := by
  unfold prj
  have h : Matrix.diagonal c = Matrix.diagonalAlgHom (n := Fin 4) (α := R) R c := rfl
  rw [h, Polynomial.aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext a
  simp [map_prod, Finset.prod_apply, Pi.algebraMap_apply]

private theorem prj_zero (c : Fin 4 → R) {i a : Fin 4} (h : a ≠ i) :
    ∏ j ∈ Finset.univ.erase i, (c a - c j) = 0 :=
  Finset.prod_eq_zero (i := a) (by simp [h]) (sub_self _)

private theorem ord_diag {H : Type} [Group H] (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R)
    (hr : ∀ g, r g = Matrix.diagonal fun i => ps i g) : Ord I ps s₀ r := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, Matrix.charpoly_diagonal]
  · intro g i j hij
    rw [hr s₀, hr g, prj_diag, prj_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_zero]
    congr 1
    funext a
    by_cases h : a = i
    · rw [prj_zero (fun a => ps a s₀) (i := j) (a := a) (by rw [h]; exact hij.ne), zero_mul, zero_mul]
    · rw [prj_zero (fun a => ps a s₀) h, mul_zero]
  · intro s _ i
    rw [hr s₀, hr s, prj_diag, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext a
    by_cases h : a = i
    · rw [h, sub_self, mul_zero, zero_mul]
    · rw [prj_zero (fun a => ps a s₀) h, mul_zero]

private theorem gsp_diag (d : Fin 4 → R) (ν : R) (h : ∀ i, d i * d i.rev = ν) : IsGSp ν (Matrix.diagonal d) := by
  have hs : ∀ i, sgn i * sgn i = 1 := by decide
  have ha : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
    ext i j
    rw [adj_apply]
    by_cases hij : i = j
    · subst hij
      simp [hs]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (fun e => hij (Fin.rev_injective e).symm), smul_zero]
  unfold IsGSp
  rw [ha, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rw [mul_comm, h]

private theorem res_self (O : Type) [CommRing O] [IsLocalRing O] [IsCO O O] (x : O) : res O O x = residue O x :=
  (res O O).commutes x

private theorem onComp_self {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsCO O O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} (P : Cond O rbar)
    (ρ : Lift O rbar O) (h : P O ρ) : OnComp P ρ.hom ρ :=
  ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ρ, h, ⟨AlgHom.id O O, fun _ _ _ => rfl⟩,
    AlgHom.id O O, Lift.ext (MonoidHom.ext fun _ => Matrix.ext fun _ _ => rfl)⟩

end Diag

theorem UpperTheory.V.GradeZeroInterpolatingElement.r0pt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∃ ρ : Lift c.O D.rbar c.O, ρ.hom = D.r0 ∧ D.IsPt ρ := by
  intro Ω _ _ _ l _ c D hD
  obtain ⟨-, -, hunr, -, hP, hrev, -, -, -, -, hcont, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hr : ∀ g, D.r0 g = Matrix.diagonal fun i => (D.ps i g : c.O) := fun _ => rfl
  have hoff : ∀ g i j, i ≠ j → D.r0 g i j = 0 := fun g i j h => by rw [hr, Matrix.diagonal_apply_ne _ h]
  have hmult : D.Mult D.r0 := fun g => by
    rw [hr]
    refine gsp_diag _ _ fun i => ?_
    rw [← hrev i]
    rfl
  have hone : ∀ g, (∀ i, D.ps i g = 1) → D.r0 g = 1 := fun g h => by
    rw [hr, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [h i]
    rfl
  let ρ : Lift c.O D.rbar c.O :=
    { hom := D.r0
      cont := fun a b => by
        by_cases h : a = b
        · subst h
          simpa only [hr, Matrix.diagonal_apply_eq] using hcont a
        · intro N
          simp only [hoff _ _ _ h]
          exact IsLocallyConstant.const _
      red := fun g a b => res_self _ _ }
  refine ⟨ρ, rfl, hmult, fun A hA g hg h1 => hone g fun i => hunr i A hA g hg h1, ⟨fun i j h => hoff _ _ _ ?_, ?_, ?_⟩,
    onComp_self _ (D.loc ρ l) ⟨fun g => hmult g, ord_diag _ _ _ _ fun g => hr g⟩,
    fun p hp => onComp_self _ (D.loc ρ p) ⟨fun g => hmult g, fun g hg => hone g fun i => ?_⟩⟩
  · rintro rfl
    exact h rfl
  · show D.r0 _ 0 2 + _ * D.r0 _ 0 2 = 0
    rw [hoff _ _ _ (by decide), hoff _ _ _ (by decide), mul_zero, add_zero]
  · show D.r0 _ 2 0 + _ * D.r0 _ 2 0 = 0
    rw [hoff _ _ _ (by decide), hoff _ _ _ (by decide), mul_zero, add_zero]
  · obtain ⟨h1, h2, h3⟩ := hP p hp g hg.1
    have h4 : D.ψ g = 1 := hg.2
    fin_cases i
    · exact h3.trans h4
    · exact h2.trans h4
    · exact h1
    · rfl
end
