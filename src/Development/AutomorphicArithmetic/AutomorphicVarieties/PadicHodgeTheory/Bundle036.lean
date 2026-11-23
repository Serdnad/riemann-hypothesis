module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle163
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_trace {k U D : Type} [Field k] [Field U] [AddCommGroup D] [Module k D]
    (m : U →+* End k D) (φ : End k D) (n : ℕ) (hn : 0 < n) (t : ℕ → U)
    (ht : ∀ i j : Fin n, t i = t j → i = j) (htn : t n = t 0)
    (hφ : ∀ i j : ℕ, φ ^ i * m (t 0 ^ j) = m (t i ^ j) * φ ^ i) (x : D) (hx : x ≠ 0) (hp : (φ ^ n) x = x) :
    ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 ∧
      φ ((∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x) = (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x := by
  have h1 : ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 := by
    by_contra hc
    push Not at hc
    letI : Module U D := Module.compHom D m
    refine hx ((Module.forall_dual_apply_eq_zero_iff U x).mp fun f => ?_)
    have h2 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := fun i : Fin n => t i)
      (v := fun i : Fin n => f ((φ ^ (i : ℕ)) x)) ht (fun j => by
        have h3 := congrArg f (hc j)

        rw [map_zero, LinearMap.sum_apply, map_sum, Finset.sum_range] at h3
        rw [← h3]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hφ, mul_comm, ← smul_eq_mul, ← map_smul]
        rfl)
    simpa using congrFun h2 ⟨0, hn⟩
  obtain ⟨j, hj⟩ := h1
  refine ⟨j, hj, ?_⟩
  have h4 : (φ ^ n * m (t 0 ^ j)) x = (φ ^ 0 * m (t 0 ^ j)) x := by
    rw [hφ, htn, End.mul_apply, hp, pow_zero, one_mul]
  have h5 := Finset.sum_range_succ (fun i => (φ ^ i * m (t 0 ^ j)) x) n
  rw [Finset.sum_range_succ', h4, add_left_inj] at h5

  rw [LinearMap.sum_apply, map_sum, ← h5]
  conv_rhs => rw [h5, ← h5]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ', mul_assoc, End.mul_apply φ]

private theorem exists_orbit (l : ℕ) [hl : Fact l.Prime] (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ↥(MaximalUnramifiedExtension l), (frobUr l ^ n) c = c ∧
      ∀ i j : Fin n, (frobUr l ^ (i : ℕ)) c = (frobUr l ^ (j : ℕ)) c → i = j := by
  have h2 := hl.out.two_le
  have hlt : ∀ i, i < n → l ^ i < l ^ n - 1 := by
    intro i hi
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    have h3 : l ^ i ≤ l ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 1 < l ^ r := Nat.one_lt_pow (by omega) (by omega)
    have h5 : l ^ r * 2 ≤ l ^ r * l := Nat.mul_le_mul_left _ h2
    rw [pow_succ]; omega
  have h0 : 0 < l ^ n - 1 := lt_of_le_of_lt (Nat.zero_le _) (hlt 0 (by omega))
  have hd : ¬ l ∣ l ^ n - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ n - 1) := ⟨h0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, h0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ n - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun i j hij => ?_⟩
  · rw [frobUr_pow_root _ _ _ h0 hd h1, show l ^ n = (l ^ n - 1) + 1 by omega, pow_succ, h1, one_mul]
  · rw [frobUr_pow_root _ _ _ h0 hd h1, frobUr_pow_root _ _ _ h0 hd h1] at hij
    have h6 : z ^ l ^ (i : ℕ) = z ^ l ^ (j : ℕ) := congrArg Subtype.val hij
    exact Fin.ext (Nat.pow_right_injective h2 (hz.pow_inj (hlt _ i.2) (hlt _ j.2) h6))

private theorem zpow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (y : D)
    (hy : (u : End k D) y = y) (n : ℤ) : ((u ^ n : (End k D)ˣ) : End k D) y = y :=
  (GlobalTheory.PstLaws.vecStab (Units.coeHom (End k D)) y).zpow_mem hy n

private theorem pow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (a : End k D) (y : D)
    (n : ℕ) (hc : Commute a ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) (ha : a y = y)
    (hy : (a * ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) y = y) : ((u : End k D) ^ n) y = y := by
  rwa [hc.eq, End.mul_apply, ha, zpow_natCast, Units.val_pow_eq_pow_val] at hy

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
  [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
  (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem exists_stab {K : FinExt l} (ρ : Representation LL ↥(GK K) V) (y : ↥(Dpst P ρ)) :
    ∃ K' : FinExt l, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → g ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) y := by
  obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
  exact ⟨K', fun g hg => Subtype.ext (hK' g hg)⟩

private theorem deg_frob_inv_pow (s : ℕ) : deg ((frob h)⁻¹ ^ s) = -(s : ℤ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := deg_mul ((frob h)⁻¹ ^ (s + 1)) (frob h)
    rw [pow_succ, inv_mul_cancel_right, ih, deg_frob] at h1
    rw [pow_succ]; push_cast; omega

variable (ρ : Representation LL ↥(GK Bw.Kw) V)

private theorem fix_of_weil (z : ↥(Dpst P ρ)) (hz : ∀ σ, actD P ρ (weilToGK Bw h σ) z = z)
    (g : ↥(GK Bw.Kw)) : actD P ρ g z = z := by
  obtain ⟨K', hK'⟩ := exists_stab P ρ z
  haveI := K'.2
  let S := (GlobalTheory.PstLaws.vecStab (actD P ρ) z).comap Bw.e.toMonoidHom
  have hS : IsOpen (S : Set ↥(Dec (F := F) A)) := by
    refine Subgroup.isOpen_mono (H₁ := ((GK K').subgroupOf (GK Bw.Kw)).comap Bw.e.toMonoidHom)
      (fun τ hτ => hK' _ hτ) ?_
    exact (IntermediateField.fixingSubgroup_isOpen K'.1).preimage (continuous_subtype_val.comp Bw.e_cont)
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  obtain ⟨τ, rfl⟩ := Bw.e.surjective g
  exact hd.induction_on (p := fun τ => τ ∈ S) τ (S.isClosed_of_isOpen hS) hz

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

include hj in
private theorem exists_period (x : ↥(Dpst P ρ)) (hx : ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ n : ℕ, 2 ≤ n ∧ (phiD P ρ ^ n) x = x := by
  have hf : resDeg l w ≠ 0 := by
    intro h0
    have hq1 := GlobalTheory.WeilDeligne.one_lt_normV w
    rw [normV_eq_pow (hj.mem_placesOver h), h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  obtain ⟨K', hK'⟩ := exists_stab P ρ x
  haveI := GlobalTheory.PstLaws.finite_quotient K' _ hK'
  haveI : (GlobalTheory.PstLaws.vecStab (actD P ρ) x).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨r, hr0, -, hr⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := GlobalTheory.PstLaws.vecStab (actD P ρ) x)) (weilToGK Bw h (frob h)⁻¹)
  have hr2 : weilToGK Bw h ((frob h)⁻¹ ^ (r * 2)) ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) x := by
    rw [map_pow (weilToGK Bw h), pow_mul]
    exact (GlobalTheory.PstLaws.vecStab (actD P ρ) x).pow_mem hr 2
  have h2 := hx ((frob h)⁻¹ ^ (r * 2))
  have e : -alpha l ((frob h)⁻¹ ^ (r * 2)) = ((resDeg l w * (r * 2) : ℕ) : ℤ) := by
    rw [alpha, deg_frob_inv_pow]; push_cast; ring
  rw [weilD_apply, e] at h2
  refine ⟨_, ?_, pow_fix (phiU P ρ) _ x _ (commute_actD_phiU P ρ _ _) hr2 h2⟩
  have : 0 < resDeg l w * r := Nat.mul_pos (Nat.pos_of_ne_zero hf) hr0
  rw [← mul_assoc]; omega

include hj in
private theorem exists_fixed_period_aux (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (hxI : ∀ s, weilD Bw h P ρ (ineIncl h s) x = x)
    (hW : ∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  obtain ⟨n, hn, hp⟩ := exists_period h Bw hj P ρ x (hW x hxI)
  obtain ⟨c, hc1, hc2⟩ := exists_orbit l n hn
  obtain ⟨j, hz0, hz1⟩ := exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2
    (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp
  refine ⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩
  refine (congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans
    (hW _ (fun s => ?_) σ)
  have hcm : Commute (weilD Bw h P ρ (ineIncl h s)) (∑ i ∈ Finset.range n, phiD P ρ ^ i *
      mulD P ρ ((frobUr l ^ 0) c ^ j)) := by
    refine Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i)
      (weilD_mulD Bw h P ρ hj _ _)
    rw [weilD_ineIncl]
    exact (phiD_actD P ρ _).symm
  exact (LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hxI s))

end

theorem UpperTheory.exists_frobenius_fixed_period :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (_hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → (∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x) → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  intro F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hxI⟩ hW
  exact exists_fixed_period_aux h Bw hj P ρ x hx0 hxI hW
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ce_ext {D W B : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group W] [Group B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (V : Subgroup D) [V.Normal] (hV : IsOpen (V : Set D))
    (hχ : ∀ s, i s ∈ V → χ s = 1) : ∃ ψ : D →* B, IsLocallyConstant ψ ∧ ∀ s, ψ (i s) = χ s := by
  set π : W →* D ⧸ V := (QuotientGroup.mk' V).comp i with hπdef
  have hopen : ∀ d : D, IsOpen {y : D | d⁻¹ * y ∈ V} := fun d =>
    hV.preimage (continuous_const_mul d⁻¹)
  have hπ : Function.Surjective π := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨s, hs⟩ := hi.exists_mem_open (hopen d) ⟨d, by simp⟩
      exact ⟨s, (QuotientGroup.eq.mpr hs).symm⟩
  have hker : π.ker ≤ χ.ker := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    apply hχ
    simpa [hπdef, QuotientGroup.eq_one_iff] using hw
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  refine ⟨((QuotientGroup.lift π.ker χ hker).comp e.symm.toMonoidHom).comp (QuotientGroup.mk' V), ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y : D | x⁻¹ * y ∈ V}, hopen x, by simp, ?_⟩
    intro y hy
    have : (QuotientGroup.mk' V y) = QuotientGroup.mk' V x := (QuotientGroup.eq.mpr hy).symm
    simp only [MonoidHom.coe_comp, Function.comp_apply, this]
  · intro s
    have h1 : QuotientGroup.mk' V (i s) = e (QuotientGroup.mk s) := rfl
    simp only [MonoidHom.coe_comp, Function.comp_apply, h1, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl

private theorem ce_eq {D W Y : Type} [TopologicalSpace D] {i : W → D} (hi : DenseRange i) {f g : D → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : ∀ s, f (i s) = g (i s)) : f = g := by
  funext x
  obtain ⟨s, hs⟩ := hi.exists_mem_open ((hf.isOpen_fiber (f x)).inter (hg.isOpen_fiber (g x))) ⟨x, rfl, rfl⟩
  have h1 : f (i s) = f x := hs.1
  have h2 : g (i s) = g x := hs.2
  rw [← h1, ← h2, h s]

private theorem ce_lim {D W R : Type} [Group D] [TopologicalSpace D] [Group W] [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (i : W →* D) (hi : DenseRange i) (χ : W →* Rˣ)
    (H : ∀ N : ℕ, ∃ ψ : D →* R ⧸ I ^ N, IsLocallyConstant ψ ∧ ∀ s, ψ (i s) = Ideal.Quotient.mk _ (χ s : R)) :
    ∃! ψ : D →* Rˣ, UpperTheory.V.Alg.AdicCont I (fun g => (ψ g : R)) ∧ ∀ s, ψ (i s) = χ s := by
  have key : ∀ x y : R, (∀ N, Ideal.Quotient.mk (I ^ N) x = Ideal.Quotient.mk (I ^ N) y) → x = y := by
    intro x y h
    rw [IsHausdorff.eq_iff_smodEq (I := I)]
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.mp (h n)
  choose φ hφc hφs using H
  let r : ℕ → D → R := fun n g => Function.surjInv Ideal.Quotient.mk_surjective (φ n g)
  have hr : ∀ n g, Ideal.Quotient.mk (I ^ n) (r n g) = φ n g := fun n g =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (φ n g)
  have hcomp : ∀ m n, m ≤ n → ∀ g, Ideal.Quotient.mk (I ^ m) (r n g) = φ m g := by
    intro m n hmn
    have hle : I ^ n ≤ I ^ m := Ideal.pow_le_pow_right hmn
    have hfun : (fun g => Ideal.Quotient.mk (I ^ m) (r n g)) = fun g => Ideal.Quotient.factor hle (φ n g) := by
      funext g
      rw [← hr n g, Ideal.Quotient.factor_mk]
    have h2 := ce_eq hi (f := fun g => Ideal.Quotient.factor hle (φ n g)) (g := fun g => φ m g)
      ((hφc n).comp _) (hφc m) (fun s => by
        show Ideal.Quotient.factor hle (φ n (i s)) = φ m (i s)
        rw [hφs n s, hφs m s, Ideal.Quotient.factor_mk])
    intro g
    exact (congrFun hfun g).trans (congrFun h2 g)
  have hlim : ∀ g, ∃ L : R, ∀ n, Ideal.Quotient.mk (I ^ n) L = φ n g := by
    intro g
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => r n g) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      apply Ideal.Quotient.eq.mp
      rw [hcomp m m le_rfl, hcomp m n hmn])
    refine ⟨L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    rw [← hr n g]
    exact (Ideal.Quotient.eq.mpr this).symm
  choose f hf using hlim
  have fmul : ∀ a b, f (a * b) = f a * f b := fun a b =>
    key _ _ fun N => by rw [map_mul, hf, hf, hf, map_mul]
  have f1 : f 1 = 1 := key _ _ fun N => by rw [hf, map_one, map_one]
  let u : D → Rˣ := fun g => ⟨f g, f g⁻¹, by rw [← fmul, mul_inv_cancel, f1], by rw [← fmul, inv_mul_cancel, f1]⟩
  let ψ : D →* Rˣ := { toFun := u, map_one' := Units.ext f1, map_mul' := fun a b => Units.ext (fmul a b) }
  have hψv : ∀ g, ((ψ g : Rˣ) : R) = f g := fun g => rfl
  have hψc : UpperTheory.V.Alg.AdicCont I (fun g => (ψ g : R)) := by
    intro N
    have : (fun g => Ideal.Quotient.mk (I ^ N) ((ψ g : Rˣ) : R)) = fun g => φ N g := funext fun g => hf g N
    rw [this]
    exact hφc N
  have hψs : ∀ s, ψ (i s) = χ s := fun s =>
    Units.ext (key _ _ fun N => by rw [hψv, hf, hφs])
  refine ⟨ψ, ⟨hψc, hψs⟩, ?_⟩
  rintro ψ' ⟨hc, hs⟩
  ext g
  refine key _ _ fun N => ?_
  have h3 := ce_eq hi (f := fun g => Ideal.Quotient.mk (I ^ N) ((ψ' g : Rˣ) : R))
    (g := fun g => Ideal.Quotient.mk (I ^ N) ((ψ g : Rˣ) : R)) (hc N) (hψc N) (fun s => by
      show Ideal.Quotient.mk (I ^ N) ((ψ' (i s) : Rˣ) : R) = Ideal.Quotient.mk (I ^ N) ((ψ (i s) : Rˣ) : R)
      rw [hs s, hψs s])
  exact congrFun h3 g

private theorem ce_open {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {B : Type} [Group B] [Finite B] (χ : Weil h →* B)
    (hχ : IsLocallyConstant fun σ : Ine (F := F) A => χ (ineIncl h σ)) :
    ∃ V : Subgroup (G F Ω), V.Normal ∧ IsOpen (V : Set (G F Ω)) ∧ ∀ s : Weil h, (s : G F Ω) ∈ V → χ s = 1 := by
  classical
  have hO : IsOpen {σ : Ine (F := F) A | χ (ineIncl h σ) = 1} := hχ.isOpen_fiber 1
  obtain ⟨O, hOo, hOeq⟩ := isOpen_induced_iff.mp hO
  have h1O : (1 : G F Ω) ∈ O := by
    have : (1 : Ine (F := F) A) ∈ {σ : Ine (F := F) A | χ (ineIncl h σ) = 1} := by simp
    rw [← hOeq] at this
    exact this
  obtain ⟨U, hUO⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  haveI hUfi : U.toSubgroup.FiniteIndex := U.toOpenSubgroup.finiteIndex_of_finite_quotient
  have he : U.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hn : 0 < Nat.card B := Nat.card_pos
  obtain ⟨ζ, hζ⟩ := GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree F Ω A w h (U.toSubgroup.index * Nat.card B)
    (Nat.mul_pos (Nat.pos_of_ne_zero he) hn)
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  have hfix := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin F {ζ})
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hfix.inter U.isOpen')
    ⟨one_mem _, one_mem U.toSubgroup⟩
  refine ⟨V.toSubgroup, inferInstance, V.isOpen', ?_⟩
  intro s hs
  have hsV := hV hs
  have hsζ : (s : G F Ω) ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hsV.1 ζ (IntermediateField.mem_adjoin_simple_self F ζ)
  have hsU : (s : G F Ω) ∈ U.toSubgroup := hsV.2
  obtain ⟨m, hm⟩ := hζ s hsζ
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hfr : χ (frob h) ^ deg s = 1 := by
    rw [hm, zpow_mul, zpow_natCast, mul_comm, pow_mul, pow_card_eq_one', one_pow, one_zpow]
  have hpow : ((frob h : Weil h) : G F Ω) ^ deg s ∈ U.toSubgroup := by
    rw [hm, zpow_mul, zpow_natCast, pow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.pow_index_mem _ _) _) _
  have hτeq : ineIncl h τ = (frob h ^ deg s)⁻¹ * s := eq_inv_mul_of_mul_eq hτ.symm
  have hτU : ((ineIncl h τ : Weil h) : G F Ω) ∈ U.toSubgroup := by
    rw [hτeq, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hpow) hsU
  have hτ1 : χ (ineIncl h τ) = 1 := by
    have : τ ∈ {σ : Ine (F := F) A | χ (ineIncl h σ) = 1} := by
      rw [← hOeq]
      exact hUO hτU
    exact this
  rw [hτ, map_mul, map_zpow, hfr, hτ1, one_mul]

theorem UpperTheory.V.Loc.charExt :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)] (ξ : (w.adicCompletion F)ˣ →* Rˣ), UpperTheory.V.Alg.AdicCont (IsLocalRing.maximalIdeal R) (fun x => (ξ x : R)) → ∃! ψ : ↥(Dec (F := F) A) →* Rˣ, UpperTheory.V.Alg.AdicCont (IsLocalRing.maximalIdeal R) (fun g => (ψ g : R)) ∧ OnArt a ψ Set.univ ξ := by
  intro _ F Ω _ _ _ _ _ A w h a ha R _ _ _ _ _ ξ hξ
  classical
  set i : Weil h →* Dec (F := F) A := Subgroup.inclusion (Weil_le_Dec h) with hi_def
  have hi : DenseRange i := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  set χ : Weil h →* Rˣ := ξ.comp a with hχ_def
  have H : ∀ N : ℕ, ∃ ψ : Dec (F := F) A →* R ⧸ IsLocalRing.maximalIdeal R ^ N, IsLocallyConstant ψ ∧
      ∀ s, ψ (i s) = Ideal.Quotient.mk _ (χ s : R) := by
    intro N
    haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := (inferInstance : Finite (IsLocalRing.ResidueField R))
    haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    let χN : Weil h →* (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ :=
      (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)).toMonoidHom).comp χ
    have hloc : IsLocallyConstant fun σ : Ine (F := F) A => χN (ineIncl h σ) := by
      refine IsLocallyConstant.desc _ (fun u : (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ => (u : R ⧸ IsLocalRing.maximalIdeal R ^ N)) ?_ Units.val_injective
      exact (hξ N).comp_continuous ha.cont
    obtain ⟨V, hVn, hVo, hV⟩ := ce_open h χN hloc
    let V' : Subgroup (Dec (F := F) A) := V.comap (Dec (F := F) A).subtype
    haveI : V'.Normal := hVn.comap _
    have hV'o : IsOpen (V' : Set (Dec (F := F) A)) := hVo.preimage continuous_subtype_val
    obtain ⟨ψ, hψl, hψ⟩ := ce_ext i hi χN V' hV'o (fun s hs => hV s hs)
    refine ⟨(Units.coeHom _).comp ψ, hψl.comp (fun u : (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ => (u : R ⧸ IsLocalRing.maximalIdeal R ^ N)), fun s => ?_⟩
    show ((ψ (i s) : (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ) : R ⧸ IsLocalRing.maximalIdeal R ^ N) = _
    rw [hψ s]
    rfl
  obtain ⟨ψ, ⟨hψc, hψs⟩, huniq⟩ := ce_lim (IsLocalRing.maximalIdeal R) i hi χ H
  refine ⟨ψ, ⟨hψc, ?_⟩, ?_⟩
  · intro s g hgs _
    have hg : g = i s := Subtype.ext hgs
    rw [hg, hψs]
    rfl
  · rintro ψ' ⟨hc, hon⟩
    exact huniq ψ' ⟨hc, fun s => hon s (i s) rfl trivial⟩
end
