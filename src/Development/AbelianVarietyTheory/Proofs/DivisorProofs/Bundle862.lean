module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle078
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle284
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle050
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle829
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

open Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.ConjCrys

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem ddR_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ DdR PD ρ, GlobalTheory.HTW.SumJumps.ext1 Qp BdR f x ∈ DdR PD ρ' := by
  intro x hx
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := hx g
  unfold actVdR at this ⊢
  rw [GlobalTheory.HTW.SumJumps.ext1_comm f (ρ g) (ρ' g) (hf g), this]

theorem finrank_ddR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (DdR PD ρ) = finrank LL (DdR PD ρ') :=
  GlobalTheory.HTW.Rec.finrank_eq_of_equiv_tensor e _ _ (ddR_map PD e.toLinearMap he)
    (ddR_map PD e.symm.toLinearMap (GlobalTheory.HTW.Rec.symm_equivariant e he))

end DdR

section Matrix

theorem mapRep_conj {Γ : Type} [Group Γ] {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S)
    (M : GL (Fin a) R) (ρ : Γ →* GL (Fin a) R) :
    mapRep f ((MulAut.conj M).toMonoidHom.comp ρ) =
      (MulAut.conj (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) R →+* Matrix (Fin a) (Fin a) S).toMonoidHom M)).toMonoidHom.comp
        (mapRep f ρ) := by
  ext g : 1
  simp [mapRep, MulAut.conj_apply, map_mul, map_inv]

variable {l : ℕ} [Fact l.Prime]

def glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) : GL (Fin n) ↥L.1 where
  val := Matrix.of fun i j => ⟨_, (hA i j).1⟩
  inv := Matrix.of fun i j => ⟨_, (hA i j).2⟩
  val_inv := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.inv_mul

theorem map_glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) :
    Units.map ((algebraMap ↥L.1 (Om l)).mapMatrix :
      Matrix (Fin n) (Fin n) ↥L.1 →+* Matrix (Fin n) (Fin n) (Om l)).toMonoidHom (glOf L A hA) = A := by
  ext i j
  rfl

end Matrix

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  (Bw : LocBridge l E Ω Gw O) {m : ℕ}

def linOf {L : Type} [Field L] (M : GL (Fin m) L) : (Fin m → L) ≃ₗ[L] (Fin m → L) :=
  LinearEquiv.ofLinear (Matrix.toLin' (M : Matrix (Fin m) (Fin m) L))
    (Matrix.toLin' ((M⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L))
    (by rw [← Matrix.toLin'_mul, M.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, M.inv_mul, Matrix.toLin'_one])

theorem linOf_repE (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) (g) (v : Fin m → ↥L.1) :
    linOf M (Bw.repE L ((MulAut.conj M⁻¹).toMonoidHom.comp r) g v) = Bw.repE L r g (linOf M v) := by
  simp only [linOf, LocBridge.repE, LinearEquiv.ofLinear_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.coeHom_apply, Matrix.toLin'_apply, inv_inv, Units.val_mul]
  erw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, M.mul_inv, Matrix.one_mul]

theorem local_conj (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) :
    (Bw.IsCrysE P L r → Bw.IsCrysE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    (Bw.IsdRE P L r → Bw.IsdRE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    ∀ τ a, Bw.multE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r) τ a = Bw.multE P L r τ a := by
  have he := linOf_repE Bw L M r
  refine ⟨fun h => GlobalTheory.HTW.Rec.isCrys_of_equiv _ (linOf M) he h, fun h => ?_, fun τ a =>
    GlobalTheory.HTW.Rec.multV_eq_of_equiv _ (linOf M) he τ a⟩
  unfold LocBridge.IsdRE at h ⊢
  rw [finrank_ddR_eq_of_equiv _ (linOf M) he, h]

variable {P Bw}

theorem exists_conj_model {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {LL' : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥LL'.1} (hm : GlobalTheory.Pst.IsModel Bw r LL' r') :
    ∃ (h : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1) (M : GL (Fin m) ↥(GlobalTheory.Pst.supExt LL' K).1),
      GlobalTheory.Pst.IsModel Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) (GlobalTheory.Pst.supExt LL' K)
        ((MulAut.conj M⁻¹).toMonoidHom.comp (mapRep (IntermediateField.inclusion h).toRingHom r')) := by
  have h1 : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_left
  have h2 : K.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_right
  have hA' : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 :=
    fun i j => ⟨h2 (hA i j).1, h2 (hA i j).2⟩
  have hm2 := hm.enlarge h1
  refine ⟨h1, glOf _ A hA', hm2.1, ?_⟩
  rw [mapRep_conj, hm2.2, map_inv, map_glOf]

theorem isCrysAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    (hr : GlobalTheory.Pst.IsCrysAt P Bw r) : GlobalTheory.Pst.IsCrysAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r', hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  exact ⟨_, _, hM, (local_conj P Bw _ M _).1 ((GlobalTheory.Pst.local_ext P Bw h r').1.2 hc)⟩

theorem isJumpsAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {τ : E →+* Om l} {J : Multiset ℤ}
    (hr : GlobalTheory.Pst.IsJumpsAt P Bw r τ J) : GlobalTheory.Pst.IsJumpsAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) τ J := by
  obtain ⟨LL', r', hm, hdR, τ', hI, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, hmult⟩ := GlobalTheory.Pst.local_ext P Bw h r'
  obtain ⟨-, hdR3, hmult3⟩ := local_conj P Bw _ M (mapRep (IntermediateField.inclusion h).toRingHom r')
  refine ⟨_, _, hM, hdR3 (hdR2.2 hdR), (IntermediateField.inclusion h).comp τ', fun x => hI x, fun n => ?_⟩
  rw [hc n, hmult3, hmult]

end Local

end GlobalTheory.ConjCrys


open GlobalTheory.ConjCrys in
theorem GlobalTheory.crysWith_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (A : GL (Fin n) (PadicAlgCl l)) (K : FinExt l) (Jm : (E →+* PadicAlgCl l) → Multiset ℤ), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1 ∧ ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1) → CrysWith r Jm → CrysWith ((MulAut.conj A⁻¹).toMonoidHom.comp r) Jm := by
  intro E Ω _ _ _ _ _ l _ n r A K Jm hA hr
  obtain ⟨hcont, hloc⟩ := hr
  refine ⟨?_, fun P AI hT w B hB O _ _ _ Bw hInd => ?_⟩
  · change Continuous fun g => A⁻¹ * r g * A⁻¹⁻¹
    exact (continuous_const.mul hcont).mul continuous_const
  · obtain ⟨h1, h2⟩ := hloc P AI hT w B hB O Bw hInd
    have e : ((MulAut.conj A⁻¹).toMonoidHom.comp r).comp (Dec (F := E) B).subtype =
        (MulAut.conj A⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) B).subtype) := MonoidHom.comp_assoc _ _ _
    rw [e]
    refine ⟨isCrysAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA h1, fun τ LL' τ' hI => ?_⟩
    exact isJumpsAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA (h2 τ LL' τ' hI)
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open Polynomial ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CharpolyFrobDense

namespace GlobalTheory.ExpFrame.CongrBlock

theorem norm_le_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (t : Γ →* Kˣ) (ht : Continuous t) (g : Γ) : ‖((t g : Kˣ) : K)‖ ≤ 1 := by
  have hc : Continuous fun g => ‖((t g : Kˣ) : K)‖ := (Units.continuous_val.comp ht).norm
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  have hpow : ∀ k : ℕ, ‖((t g : Kˣ) : K)‖ ^ k ≤ M := fun k => by
    have := hM ⟨g ^ k, Set.mem_univ _, rfl⟩
    simpa [map_pow, Units.val_pow_eq_pow_val, norm_pow] using this
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop M).exists
  exact absurd (hpow k) (not_le.2 hk)

theorem continuous_character_of_rankOneRep_continuous {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    (χ : Γ →* Kˣ) (h : Continuous (GlobalTheory.TripleGal.rk1 χ)) : Continuous fun g => ((χ g : Kˣ) : K) := by
  have h1 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 :=
    (Units.continuous_val.comp h).matrix_elem 0 0
  convert h1 using 1
  funext g
  simp [GlobalTheory.TripleGal.rk1]

theorem coeff_heckePolyOf {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) (j : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff j =
      if j ≤ n then (-1) ^ j * (q : L) ^ (j * (j - 1) / 2) * a j else 0 := by
  simp only [Formalism.L2.Col.heckePolyOf, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_iff]

theorem coeff_sub_eq_reverse {K : Type} [Field K] {p q : K[X]} {n : ℕ} (hp : p.natDegree = n)
    (hq : q.natDegree = n) (k : ℕ) (hk : k ≤ n) :
    (p - q).coeff k = (p.reverse - q.reverse).coeff (n - k) := by
  simp only [coeff_sub, coeff_reverse, hp, hq, revAt_le (Nat.sub_le n k), Nat.sub_sub_self hk]

theorem norm_sysOf_sub_lt {l : ℕ} [Fact l.Prime] {Pl I : Type} (n : ℕ) (pt : Pl → Fin n → I) {θ θ0 : I → Qbar l}
    (h : ∀ i, ‖θ i - θ0 i‖ < 1) (P : Pl) (k : ℕ) : ‖sysOf n pt θ P k - sysOf n pt θ0 P k‖ < 1 := by
  unfold sysOf
  split_ifs
  · exact h _
  · simp

theorem norm_coeff_hecke_sub_lt {l : ℕ} [Fact l.Prime] (n q : ℕ) (a b : ℕ → Qbar l) (w : Qbar l) (hw : ‖w‖ ≤ 1)
    (hab : ∀ k, ‖a k - b k‖ < 1) (j : ℕ) :
    ‖(Formalism.L2.Col.heckePolyOf n q (fun k => a k * w ^ k) -
      Formalism.L2.Col.heckePolyOf n q (fun k => b k * w ^ k)).coeff j‖ < 1 := by
  rw [coeff_sub, coeff_heckePolyOf, coeff_heckePolyOf]
  split_ifs
  · have e : (-1) ^ j * (q : Qbar l) ^ (j * (j - 1) / 2) * (a j * w ^ j) -
        (-1) ^ j * (q : Qbar l) ^ (j * (j - 1) / 2) * (b j * w ^ j) =
        (-1) ^ j * ((q : Qbar l) ^ (j * (j - 1) / 2) * w ^ j) * (a j - b j) := by ring
    rw [e, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow, norm_pow]
    have h1 : ‖(q : Qbar l)‖ ^ (j * (j - 1) / 2) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    have h2 : ‖w‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
    calc _ ≤ ‖a j - b j‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ h1 (pow_nonneg (norm_nonneg _) _) h2)
      _ < 1 := hab j
  · simp

theorem blockFor_of_congr : GlobalTheory.Published.ChebotarevDegreeOne → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (F : Frame l ι P.Nr) (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (mu : ι → ℕ → ℕ) (θ θ0 : F.I → PadicAlgCl l), (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → F.IsEig W.lam θ0 → Bk θ0 → (∀ i, ‖θ i - θ0 i‖ < 1) → BlockFor Ω inc P W mu := by
  intro hC E Ω _ _ _ _ _ _ l _ ι _ inc P W F Bk hG mu θ θ0 hmu hθ hθ0 hBk hcl
  obtain ⟨Pl, pt, Fn, ep, hep, h1, h2⟩ := hG
  obtain ⟨r, J, hJ, hr, hrR⟩ := h1 mu θ hmu hθ
  obtain ⟨a, ρ, χ, bot, hat, hρ, hχ, hbot, hρR⟩ := h2 θ0 hθ0 hBk
  refine ⟨ep, J, bot, hep, ⟨r, a, ρ, χ, hat, hr, hρ, hχ, ?_⟩, fun τ => ⟨fun b => hJ τ b, hbot τ⟩⟩

  set p : G E Ω → Polynomial (Qbar l) := fun σ => (r σ).val.charpoly with hp
  set q : G E Ω → Polynomial (Qbar l) := fun σ =>
    (ρ σ).val.charpoly * ∏ s, (X - C ((χ s σ : (Qbar l)ˣ) : Qbar l)) with hq
  have dp : ∀ σ, (p σ).natDegree = P.Nr := fun σ => by
    simp [hp, Matrix.charpoly_natDegree_eq_dim]
  have dq : ∀ σ, (q σ).natDegree = P.Nr := fun σ => by
    simp only [hq]
    rw [(Matrix.charpoly_monic _).natDegree_mul (monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _),
      Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin, hat]

  have cp : CoeffCont p := fun k =>
    (GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix P.Nr k).comp (Units.continuous_val.comp hr.1)
  have cq : CoeffCont q := by
    have c1 : CoeffCont fun σ : G E Ω => (ρ σ).val.charpoly := fun k =>
      (GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix a k).comp (Units.continuous_val.comp hρ)
    have c2 := coeffCont_prod Finset.univ (fun s (σ : G E Ω) => (X - C ((χ s σ : (Qbar l)ˣ) : Qbar l)))
      (fun s _ => coeffCont_X_sub_C (continuous_character_of_rankOneRep_continuous (χ s) (hχ s).1))
    exact c1.mul c2

  set good : G E Ω → Prop := fun σ => ∀ k, ‖(p σ - q σ).coeff k‖ < 1 with hgood
  have hclosed : IsClosed {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} := by
    have : {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} =
        ⋂ k, (fun σ : G E Ω => (p (σ ^ (Fn.sgn : ℤ)) - q (σ ^ (Fn.sgn : ℤ))).coeff k) ⁻¹' Metric.ball 0 1 := by
      ext σ; simp [hgood]
    rw [this]
    refine isClosed_iInter fun k => (IsUltrametricDist.isClosed_ball (0 : Qbar l) 1).preimage ?_
    have hz := continuous_zpow (G := G E Ω) (Fn.sgn : ℤ)
    simp only [coeff_sub]
    exact ((cp k).comp hz).sub ((cq k).comp hz)

  have hS := Fn.cofin
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) hC hS
  have hsub : {σ : G E Ω | ∃ v : HeightOneSpectrum (𝓞 E),
      v ∉ {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range Fn.lab} ∧
      v.asIdeal.inertiaDeg ℤ = 1 ∧ ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ IsFrob B (normV v) σ} ⊆
      {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} := by
    rintro σ ⟨v, hv, hd, B, hB, hσ⟩
    have hpr : (Ideal.absNorm v.asIdeal).Prime := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    have hv' : v ∈ Set.range Fn.lab := by
      by_contra h; exact hv ⟨hpr, h⟩
    obtain ⟨P0, rfl⟩ := hv'
    have e1 := hrR P0 B σ hB hσ
    have e2 := hρR P0 B σ hB hσ
    have hw := norm_le_one_of_compact Fn.tw Fn.cont (σ ^ (Fn.sgn : ℤ))
    intro k
    by_cases hk : k ≤ P.Nr
    · rw [coeff_sub_eq_reverse (dp _) (dq _) k hk]
      simp only [hp, hq]
      rw [e1, e2]
      exact norm_coeff_hecke_sub_lt _ _ _ _ _ hw (norm_sysOf_sub_lt P.Nr pt hcl P0) _
    · push_neg at hk
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by rw [dp]; exact hk),
        coeff_eq_zero_of_natDegree_lt (by rw [dq]; exact hk)]
      simp
  have hall : ∀ σ : G E Ω, good (σ ^ (Fn.sgn : ℤ)) := fun σ => by
    have h := closure_minimal hsub hclosed
    rw [hD.closure_eq] at h
    exact h (Set.mem_univ σ)
  intro σ k
  have h := hall (σ ^ (Fn.sgn : ℤ)) k
  have e : (σ ^ (Fn.sgn : ℤ)) ^ (Fn.sgn : ℤ) = σ := by
    rw [← zpow_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, zpow_one]
  rw [e] at h
  exact h

end GlobalTheory.ExpFrame.CongrBlock
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_movedPoint : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (z : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → (∀ i, 1 + z i * c ≠ 0 ∧ 0 < (τ + t * z i / (1 + z i * c)).im) → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  first | exact @GlobalTheory.HilbFam.hasSum_movedPoint | exact GlobalTheory.HilbFam.hasSum_movedPoint | (intros; apply GlobalTheory.HilbFam.hasSum_movedPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.FODef

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem sqZero : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0 := by
  rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  change TrivSqZeroExt.fst r = 0 at hr
  change TrivSqZeroExt.fst s = 0 at hs
  rw [Submodule.mem_bot]
  ext
  · simp [hr, hs]
  · simp [hr, hs]

theorem constMorV (A₀ : Over (Sp k)) [GrpObj A₀] :
    GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ (sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
      (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
  GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
    (by
      rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
      congr 1) (𝟙 A₀)

variable {k V}

def IsFilLiftV {A₀ : Over (Sp k)} [GrpObj A₀] {A : Over (Sp (TrivSqZeroExt k V))} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) i)
    (x : HdR A₀) (y : primDR A₀ →ₗ[k] V) : Prop :=
  ∃ d ∈ liftFil (divided₂ (sqZero k V)) h, ∀ c : primDR A₀,
    d ((constMorV k V A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c)

end GlobalTheory.FODef

namespace GlobalTheory.HTUniv

theorem coord {k : Type} [Field k] {d : ℕ} (c : (Fin d → k) →ₗ[k] k) (v : Fin d → k) :
    c v = ∑ j, v j * c (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Pi.single j (v j) = v j • (Pi.single j (1 : k) : Fin d → k) := by
    ext i; simp [Pi.single_apply]
  rw [e, map_smul, smul_eq_mul]

theorem comp_pi {k : Type} [Field k] {d : ℕ} {P : Type*} [AddCommGroup P] [Module k P]
    (c : (Fin d → k) →ₗ[k] k) (y : Fin d → (P →ₗ[k] k)) :
    c ∘ₗ LinearMap.pi y = ∑ j, c (Pi.single j 1) • y j := by
  refine LinearMap.ext fun q => ?_
  rw [LinearMap.comp_apply, coord c, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.pi_apply, smul_eq_mul, mul_comm]

theorem sum_proj_single {k : Type} [Field k] {d : ℕ} (c₀ : Fin d → k) (j : Fin d) :
    (∑ i, c₀ i • LinearMap.proj (R := k) (φ := fun _ : Fin d => k) i) (Pi.single j 1) = c₀ j := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try exact mul_one _

end GlobalTheory.HTUniv
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

def IsPure {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (W : A ⟶ A) [IsMonHom W] (r s : R) : Prop :=
  (∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W x = r • x) ∧ ∀ y : HdR A, push (dp0 R) (𝟙 _) W y - s • y ∈ Fil A

def IsPureBC {S : Type} [CommRing S] (G : Over (Sp S)) [GrpObj G] (W : G ⟶ G) (r s : S) : Prop :=
  ∀ (R : Type) [CommRing R] (f : S →+* R) (A : Over (Sp R)) [GrpObj A] (φ : A.left ⟶ G.left),
    IsGrpPullback A G (spMap f) φ → ∀ (W' : A ⟶ A) [IsMonHom W'], W'.left ≫ φ = φ ≫ W.left → IsPure A W' (f r) (f s)

theorem IsPure.mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {W : A ⟶ A} [IsMonHom W] {r r' s : R}
    (h : IsPure A W r' s) (hu : IsUnit (r - s)) {y : HdR A} (hy : push (dp0 R) (𝟙 _) W y = r • y) : y ∈ Fil A := by
  have hm := h.2 y
  rw [hy, ← sub_smul] at hm
  obtain ⟨u, hu'⟩ := hu
  have hv := (Fil A).smul_mem (↑u⁻¹ : R) hm
  rwa [smul_smul, ← hu', Units.inv_mul, one_smul] at hv

end GlobalTheory.PureLift
end
end

section

open IsLocalRing GlobalTheory.Toroidal

theorem _root_.GlobalTheory.T.exists_extension_etaleCompletion_to_complete_local : ∀ (O R' E Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [Field Ω] (φ' : O →+* R') (ψ : O →+* E) (u' : R' →+* Ω) (v : E →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → IsAdicComplete (maximalIdeal E) E → IsLocalHom ψ → RingHom.ker u' = maximalIdeal R' → RingHom.ker v = maximalIdeal E → v.comp ψ = u'.comp φ' → (∀ r : R', u' r ∈ v.range) → ∃ b : R' →+* E, b.comp φ' = ψ ∧ v.comp b = u' := by
  first | exact @GlobalTheory.EtaleCompletionLift.exists_extension | exact GlobalTheory.EtaleCompletionLift.exists_extension | (intros; apply GlobalTheory.EtaleCompletionLift.exists_extension <;> assumption)
end
